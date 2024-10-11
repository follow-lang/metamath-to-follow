import io
import json
import re

from lark import Lark


class Grammar:
    def __init__(self, file: io.TextIOWrapper):
        (
            self.grammar_map,
            self.type_map,
            self.constant_map,
            self.types,
            self.without_constant_term,
        ) = self.prepare(file)

    def generate_parser(self, toks: list[str] = None):
        grammar = self.generate_grammar(toks)
        parser = Lark(grammar)
        return parser

    def generate_grammar(self, toks: list[str] = None):
        type_labels: dict[str, list[str]] = {}
        output_gramar = [
            "%import common.WS_INLINE   -> WS_INLINE",
            "%ignore WS_INLINE",
        ]
        label_record: set[str] = set()
        if toks is None:
            toks = self.constant_map.keys()
        else:
            # 每个类型兜底一个变量
            for t in self.types:
                toks.add(f"v{t[0]}0")
        for tok in toks:
            labels = self.constant_map.get(tok, [])
            for label in labels:
                if label in label_record:
                    continue
                label_record.add(label)
                output_gramar.append(self.grammar_map.get(label))
                type = self.type_map.get(label)
                if type in type_labels:
                    type_labels[type].append(label)
                else:
                    type_labels[type] = [label]
        # 简化版本，没有用到常数的term默认加入到grammar中
        # 按条件加入到grammar中好麻烦
        for label, type in self.without_constant_term:
            if label not in label_record:
                output_gramar.append(self.grammar_map.get(label))
                if type in type_labels:
                    type_labels[type].append(label)
                else:
                    type_labels[type] = [label]
        for type, labels in type_labels.items():
            output_gramar.append(type + ": " + " | ".join(labels))
        output_gramar.append("start: " + " | ".join(type_labels.keys()))
        return "\n".join(output_gramar)

    def prepare(self, file: io.TextIOWrapper):
        constants: set[str] = set()
        types: set[str] = set()
        variable_map: dict[str, str] = {}  # (value, type)

        grammar_map: dict[str, str] = {}  # (label, grammar)
        type_map: dict[str, str] = {}  # (label, type)
        constant_map: dict[str, list[str]] = {}  # (constant, labels)
        without_constant_term: set[tuple[str, str]] = set()
        for block_type, props in scan(file):
            if block_type == "$c":
                constants.add(props)
            elif block_type == "$f":
                _, f_type, f_value = props
                variable_map[f_value] = f_type
                types.add(f_type)
            elif block_type == "$a":
                a_label, a_type, a_stmt = props
                a_label = encode_label(a_label)
                types.add(a_type)
                grammar_map[a_label] = stmt_to_grammar(a_label, a_stmt, variable_map)
                type_map[a_label] = a_type
                without_constant = True
                for tok in a_stmt:
                    if tok not in variable_map:
                        without_constant = False
                        if tok not in constant_map:
                            constant_map[tok] = [a_label]
                        else:
                            constant_map[tok].append(a_label)
                if without_constant:
                    without_constant_term.add((a_label, a_type))
        for type in types:
            for i in range(100):
                label = "v" + type[0] + str(i)
                grammar_map[label] = f'{label}: "{label}"'
                type_map[label] = type
                if label not in constant_map:
                    constant_map[label] = [label]
                else:
                    constant_map[label].append(label)
        return grammar_map, type_map, constant_map, types, without_constant_term


def generate_stmt_parser(file: io.TextIOWrapper):
    grammar = generate_grammar(file)
    parser = Lark(grammar)
    return parser


def generate_grammar(file: io.TextIOWrapper):
    constants: set[str] = set()
    types: set[str] = set()
    variable_map: dict[str, str] = {}  # (value, type)
    type_map: dict[str, list[str]] = {}  # (type, [label...])
    grammars: list[str] = [
        "%import common.WS_INLINE   -> WS_INLINE",
        "%ignore WS_INLINE",
    ]
    for block_type, props in scan(file):
        if block_type == "$c":
            constants.add(props)
        elif block_type == "$f":
            _, f_type, f_value = props
            variable_map[f_value] = f_type
            types.add(f_type)
        elif block_type == "$a":
            a_label, a_type, a_stmt = props
            a_label = encode_label(a_label)
            types.add(a_type)
            if a_type in type_map:
                type_map[a_type].append(a_label)
            else:
                type_map[a_type] = [a_label]
            grammars.append(stmt_to_grammar(a_label, a_stmt, variable_map))
    for type in types:
        for i in range(20):
            label = "v" + type[0] + str(i)
            grammars.append(f'{label}: "{label}"')
            if type in type_map:
                type_map[type].append(label)
            else:
                type_map[type] = [label]
        grammars.append(f"{type}: " + " | ".join(type_map[type]))
    grammars.append("start: " + " | ".join(type_map.keys()))
    return "\n".join(grammars)


def encode_label(label):
    label = label.replace(".", "_d_").replace("-", "_b_")  # 替换特殊字符
    label = re.sub(r"(?<!^)(?=[A-Z])", "_u", label)  # 在大写字母前加下划线
    label = re.sub(r"(?<=[A-Z])", "_", label)  # 在大写字母后加下划线
    if label and label[0].isupper():
        label = f"_u{label}"
    return label.lower()


def decode_label(label):
    label = label.replace("_d_", ".").replace("_b_", "-")
    label = re.sub(r"_u([a-z])", lambda m: m.group(1).upper(), label)
    label = re.sub(r"([A-Z])_", lambda m: m.group(1), label)
    return label


def stmt_to_grammar(label, stmt, variable_map):
    result = []
    for token in stmt:
        if token in variable_map:
            result.append(variable_map[token])
        else:
            result.append(json.dumps(token))
    return label + ": " + " ".join(result)


def scan(file: io.TextIOWrapper):
    """
    简化版本scan，用于生成grammar
    """
    in_comment_block = False
    in_const_block = False
    in_float_block = False
    in_axiom_block = False
    floattokens = []
    axiomtokens = []
    label = None

    line = file.readline()

    while line:
        tokens = line.split()
        for token in tokens:
            if in_comment_block:
                if token == "$)":
                    in_comment_block = False
            elif in_const_block:
                if token == "$.":
                    in_const_block = False
                else:
                    yield ("$c", token)
            elif in_float_block:
                if token == "$.":
                    if len(floattokens) == 2:
                        yield (
                            "$f",
                            (label, floattokens[0], floattokens[1]),
                        )  # ("$f", (label, type, value))
                    in_float_block = False
                    floattokens = []
                else:
                    if len(floattokens) < 2:
                        floattokens.append(token)
            elif in_axiom_block:
                if token == "$.":
                    if len(axiomtokens) > 1:
                        yield (
                            "$a",
                            (
                                label,
                                axiomtokens[0],
                                axiomtokens[1:],
                            ),
                        )  # ("$a", (label, type, stmt))
                    in_axiom_block = False
                    axiomtokens = []
                else:
                    if len(axiomtokens) == 0 or axiomtokens[0] != "|-":
                        axiomtokens.append(token)
            elif token == "$(":
                in_comment_block = True
            elif token == "$c":
                in_const_block = True
            elif token == "$f":
                in_float_block = True
            elif token == "$a":
                in_axiom_block = True
            else:
                label = token
        line = file.readline()
