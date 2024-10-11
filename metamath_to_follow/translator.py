import argparse
import io
import itertools
import json
import logging  # 添加日志模块
import os
import typing

from lark import Lark, Tree

from metamath_to_follow.generate_grammar import Grammar, decode_label

logging.basicConfig(filename="error.log", level=logging.ERROR)  # 配置日志


def transform(file: io.TextIOWrapper, grammar: Grammar | None = None):
    fs = FrameStack()
    fs.push()
    global_labels: dict[Label, any] = {}

    types: set[str] = set(["|-"])

    for btype, props in scan(file):
        if btype == "${":
            fs.push()
        elif btype == "$}":
            fs.pop()
        elif btype == "$c":
            fs.add_c(props)
        elif btype == "$v":
            fs.add_v(props)
        elif btype == "$f":
            fs.add_f(*props)
            global_labels[props[0]] = ("$f", props)
            if props[1] not in types:
                types.add(props[1])
                content, trajectory = type_content(props[1])
                yield (props[1], content, trajectory)
        elif btype == "$e":
            fs.add_e(*props)
            global_labels[props[0]] = ("$e", props)
            if props[1] not in types:
                types.add(props[1])
                content, trajectory = type_content(props[1])
                yield (props[1], content, trajectory)
        elif btype == "$a":
            label, type, stmt = props
            assertion, extension = fs.make_assertion(stmt, grammar, types)
            global_labels[label] = ("$a", (type, assertion, extension))
            if props[1] != "|-":
                if props[1] not in types:
                    types.add(props[1])
                    content, trajectory = type_content(props[1])
                    yield (props[1], content, trajectory)
                content, trajectory = term_content(label, type, stmt, extension)
                yield (label, content, trajectory)
            else:
                content, trajectory = axiom_content(label, assertion, extension)
                yield (label, content, trajectory)
        elif btype == "$p":
            label, type, stmt, proof = props
            assertion, extension = fs.make_assertion(stmt, grammar, types)
            proof = decompress_proof(assertion, extension, proof, global_labels)
            global_labels[label] = ("$p", (type, assertion, extension))
            if props[1] != "|-":
                if props[1] not in types:
                    types.add(props[1])
                    content, trajectory = type_content(props[1])
                    yield (props[1], content, trajectory)
                # 不需要content
            else:
                content, trajectory = thm_content(
                    label, assertion, extension, proof, global_labels
                )
                if content is not None:
                    yield (label, content, trajectory)


def type_content(type):
    output = [f"type {type}"]
    for idx in range(20):
        output.append(f"term {type} g{type[0]}{idx}")

    trajectory = {"type": "type", "label": type}
    return "\n".join(output), json.dumps(trajectory)


def term_content(label, type, stmt, extension):
    arguments = extension[1]
    argument_type_map = extension[2]
    argument_alias_map = extension[3]
    args = []
    for value in arguments:
        args.append(argument_type_map[value] + " " + argument_alias_map[value])
    new_stmt = [argument_alias_map.get(tok, tok) for tok in stmt]
    if len(args) > 0:
        output = ["term", type, label + "(" + ",".join(args) + ")", "{", *new_stmt, "}"]
    else:
        output = ["term", type, label, "{", *new_stmt, "}"]
    trajectory = {
        "type": "term",
        "label": label,
        "type": type,
        "args": args,
        "stmt": " ".join(new_stmt),
    }

    return " ".join(output), json.dumps(trajectory)


def axiom_content(label, assertion, extension):
    arguments = extension[1]
    argument_type_map = extension[2]
    argument_alias_map = extension[3]
    ext_e_hyps = extension[-2]
    ext_stmt = extension[-1]
    difflists = extension[0]
    dvs = assertion[0]

    args = []
    for value in arguments:
        args.append(argument_type_map[value] + " " + argument_alias_map[value])
    head = " ".join(["axiom", label + "(" + ",".join(args) + ")", "{"])
    output = [head]

    new_stmt, new_ehyps, new_dvs = stmt_subs(
        ext_stmt, ext_e_hyps, dvs, argument_alias_map, argument_alias_map
    )
    output.append("|- " + new_stmt)
    for ehyp in new_ehyps:
        output.append("-| " + ehyp)

    if len(difflists) > 0:
        diffcontent = ["diff"]
        for difflist in difflists:
            diffcontent.append(
                "(" + ",".join([argument_alias_map.get(v, v) for v in difflist]), ")"
            )
        output.append(" ".join(diffcontent))

    output.append("}")

    trajectory = {
        "type": "axiom",
        "label": label,
        "args": args,
        "target": new_stmt,
        "conditions": new_ehyps,
        "dvs": list(new_dvs),
    }

    return "\n".join(output), json.dumps(trajectory)


def thm_content(label, assertion, extension, proof, global_labels):
    arguments = extension[1]
    argument_type_map = extension[2]
    argument_alias_map = extension[3]
    ext_e_hyps = extension[-2]
    ext_stmt = extension[-1]
    difflists = extension[0]

    dvs = assertion[0]

    args = []
    for value in arguments:
        args.append(argument_type_map[value] + " " + argument_alias_map[value])
    head = " ".join(["thm", label + "(" + ",".join(args) + ")", "{"])
    output = [head]
    new_stmt, new_ehyps, new_dvs = stmt_subs(
        ext_stmt, ext_e_hyps, dvs, argument_alias_map, argument_alias_map
    )
    output.append("|- " + new_stmt)
    for ehyp in new_ehyps:
        output.append("-| " + ehyp)
    if len(difflists) > 0:
        diffcontent = ["diff"]
        for difflist in difflists:
            diffcontent.append(
                "(" + ",".join([argument_alias_map.get(v, v) for v in difflist]), ")"
            )
        output.append(" ".join(diffcontent))

    output.append("} = {")

    new_proof, actions = transform_proof(proof, global_labels, argument_alias_map)
    states = generate_state(new_stmt, new_ehyps, new_dvs, actions)

    if len(new_proof) == 0:
        # 排除没有证明的proof
        print(label, "invalid proof")
        return None, None

    # 在适当的位置添加日志记录
    if len(states[-1]) != 0:
        logging.error("证明异常", label)  # 记录错误信息

    for op in new_proof:
        output.append("  " + op)
    output.append("}")

    trajectory = {
        "type": "thm",
        "label": label,
        "args": args,
        "target": new_stmt,
        "conditions": new_ehyps,
        "dvs": list(new_dvs),
        "states": states,
        "actions": [
            (a_stmt, a_ehyps, list(a_dvs)) for a_stmt, a_ehyps, a_dvs in actions
        ],
        "operators": new_proof,
    }

    return "\n".join(output), json.dumps(trajectory)


def generate_state(init_target, init_assumptions, init_dvs, actions):
    output_state = [[init_target]]
    cur_state = [init_target]
    for a_stmt, a_ehyps, a_dvs in actions:
        if a_stmt not in cur_state:
            continue
        cur_state.remove(a_stmt)
        for ehyp in a_ehyps:
            if ehyp not in init_assumptions:
                cur_state.append(ehyp)
        for d in a_dvs:
            if d not in init_dvs:
                cur_state.append(f"diff ({d[0]},{d[1]})")
        output_state.append([*cur_state])
    return output_state


def transform_proof(proof, global_labels, argument_alias_map):
    output = []
    stack = []
    global_type_idx_record = {}
    global_argument_alias_map: dict[str, str] = {}
    output_actions = []
    for label in proof:
        btype, props = global_labels[label]
        if btype == "$f":
            _, type, value = props
            if value in argument_alias_map:
                stack.append(argument_alias_map.get(value))
            elif value in global_argument_alias_map:
                stack.append(global_argument_alias_map.get(value))
            else:
                if type in global_type_idx_record:
                    alias = "g" + type[0] + str(global_type_idx_record[type])
                    global_type_idx_record[type] += 1
                else:
                    alias = "g" + type[0] + str(0)
                    global_type_idx_record[type] = 1
                global_argument_alias_map[value] = alias
                stack.append(alias)
        elif btype == "$a":
            type, (dvs, f_hyps, _, _), extension = props
            ext_stmt = extension[-1]
            argument = extension[1]
            n_args = len(f_hyps)
            args = stack[len(stack) - n_args :]
            if n_args > len(stack):
                print("args error", stack, args, f_hyps, label)
                return None, None
            arg_map = {f_value: args[idx] for idx, (_, f_value) in enumerate(f_hyps)}
            del stack[len(stack) - n_args :]
            if type != "|-":
                if len(argument) > 0:
                    new_args = [arg_map[value] for value in argument]
                    op = label + "(" + ",".join(new_args) + ")"
                else:
                    op = label
                stack.append(op)
            else:
                op = "".join([arg_map.get(tok, tok) for tok in ext_stmt])
                new_args = [arg_map[value] for value in argument]
                output.append(label + "(" + ",".join(new_args) + ")")
                # 压入 output_action_state，由 (action, state)
                ext_ehyps = extension[-2]
                new_stmt, new_ehyps, new_dvs = stmt_subs(
                    ext_stmt, ext_ehyps, dvs, arg_map, argument_alias_map
                )
                output_actions.append((new_stmt, new_ehyps, new_dvs))
        elif btype == "$p":
            type, (dvs, f_hyps, _, _), extension = props
            ext_stmt = extension[-1]
            argument = extension[1]
            n_args = len(f_hyps)
            if n_args > len(stack):
                print("args error", stack, args, f_hyps, label)
                return None, None
            args = stack[len(stack) - n_args :]
            del stack[len(stack) - n_args :]
            arg_map = {f_value: args[idx] for idx, (_, f_value) in enumerate(f_hyps)}
            op = "".join([arg_map.get(tok, tok) for tok in ext_stmt])
            new_args = [arg_map[value] for value in argument]
            output.append(label + "(" + ",".join(new_args) + ")")
            # 压入 output_action_state，由 (action, state)
            ext_ehyps = extension[-2]
            new_stmt, new_ehyps, new_dvs = stmt_subs(
                ext_stmt, ext_ehyps, dvs, arg_map, argument_alias_map
            )
            if type != "|-":
                stack.append(new_stmt)
            else:
                output_actions.append((new_stmt, new_ehyps, new_dvs))
    return output[::-1], output_actions[::-1]


def stmt_subs(stmt, ehyps, dvs, arg_map, argument_alias_map):
    values = set(argument_alias_map.values())
    arg_value_map = {
        k: set([word for word in expr if word in values]) for k, expr in arg_map.items()
    }
    new_stmt = "".join([arg_map.get(word, word) for word in stmt])
    new_ehyps = ["".join([arg_map.get(word, word) for word in ehyp]) for ehyp in ehyps]
    new_diffs = set()
    for v1, v2 in dvs:
        v1set = arg_value_map.get(v1)
        v2set = arg_value_map.get(v2)
        for x, y in itertools.product(v1set, v2set):
            new_diffs.add((min(x, y), max(x, y)))
    return new_stmt, new_ehyps, new_diffs


def decompress_proof(assertion, extension, proof, global_labels):
    if proof[0] != "(":  # not compressed proof
        return proof

    _, _, _, _, f_labels, e_labels, _, _ = extension

    labels = f_labels + e_labels
    hyp_end = len(labels)

    ep = proof.index(")")
    labels += proof[1:ep]
    compressed_proof = "".join(proof[ep + 1 :])

    proof_ints = []
    cur_int = 0

    for ch in compressed_proof:
        if ch == "Z":
            proof_ints.append(-1)
        elif "A" <= ch and ch <= "T":
            cur_int = 20 * cur_int + ord(ch) - ord("A") + 1
            proof_ints.append(cur_int - 1)
            cur_int = 0
        elif "U" <= ch and ch <= "Y":
            cur_int = 5 * cur_int + ord(ch) - ord("U") + 1

    label_end = len(labels)
    decompressed_ints = []
    subproofs = []
    prev_proofs = []
    for pf_int in proof_ints:
        if pf_int == -1:
            subproofs.append(prev_proofs[-1])
        elif 0 <= pf_int and pf_int < hyp_end:
            prev_proofs.append([pf_int])
            decompressed_ints.append(pf_int)
        elif hyp_end <= pf_int and pf_int < label_end:
            decompressed_ints.append(pf_int)

            step = global_labels[labels[pf_int]]
            step_type, step_data = step[0], step[1]
            if step_type in ("$a", "$p"):
                _, assertion, extension = step_data
                sd, svars, shyps, sresult = assertion
                nshyps = len(svars) + len(shyps)
                if nshyps != 0:
                    new_prevpf = [s for p in prev_proofs[-nshyps:] for s in p] + [
                        pf_int
                    ]
                    prev_proofs = prev_proofs[:-nshyps]
                else:
                    new_prevpf = [pf_int]
                prev_proofs.append(new_prevpf)
            else:
                prev_proofs.append([pf_int])
        elif pf_int - label_end < len(subproofs):
            pf = subproofs[pf_int - label_end]
            decompressed_ints += pf
            prev_proofs.append(pf)
    return [labels[i] for i in decompressed_ints]


def scan(file: io.TextIOWrapper):
    in_comment_block = False
    in_const_block = False
    in_var_block = False
    in_diff_block = False
    in_float_block = False
    in_essential_block = False
    in_axiom_block = False
    in_thm_block = False
    in_proof_block = False
    difftokens = []
    floattokens = []
    essentialtokens = []
    axiomtokens = []
    thmtokens = []
    prooftokens = []
    label = None

    line = file.readline()

    while line:
        tokens = line.split()
        for token in tokens:
            if in_comment_block:
                if token == "$)":
                    in_comment_block = False
            elif token == "$(":
                in_comment_block = True
            elif in_const_block:
                if token == "$.":
                    in_const_block = False
                else:
                    yield ("$c", token)
            elif in_var_block:
                if token == "$.":
                    in_var_block = False
                else:
                    yield ("$v", token)
            elif in_diff_block:
                if token == "$.":
                    yield ("$d", difftokens)
                    in_diff_block = False
                    difftokens = []
                else:
                    difftokens.append(token)
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
            elif in_essential_block:
                if token == "$.":
                    if len(essentialtokens) > 1:
                        yield ("$e", (label, essentialtokens[0], essentialtokens[1:]))
                    in_essential_block = False
                    essentialtokens = []
                else:
                    essentialtokens.append(token)
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
                    axiomtokens.append(token)
            elif in_thm_block:
                if token == "$=":
                    in_thm_block = False
                    in_proof_block = True
                else:
                    thmtokens.append(token)
            elif in_proof_block:
                if token == "$.":
                    if len(thmtokens) > 1 and len(prooftokens) > 0:
                        yield (
                            "$p",
                            (label, thmtokens[0], thmtokens[1:], prooftokens),
                        )  # ("$p", (label, type, stmt, proof))
                    in_proof_block = False
                    thmtokens = []
                    prooftokens = []
                else:
                    prooftokens.append(token)
            elif token == "$c":
                in_const_block = True
            elif token == "$v":
                in_var_block = True
            elif token == "$d":
                in_diff_block = True
            elif token == "$f":
                in_float_block = True
            elif token == "$e":
                in_essential_block = True
            elif token == "$a":
                in_axiom_block = True
            elif token == "$p":
                in_thm_block = True
            elif token == "${":
                yield ("${", None)
            elif token == "$}":
                yield ("$}", None)
            else:
                label = token
        line = file.readline()


Type = str
Symbol = str
Label = str


class Frame:
    def __init__(self) -> None:
        """Construct an empty frame."""
        self.constants: set[Symbol] = set()
        self.variables: set[Symbol] = set()
        self.diffs: list[list[Symbol]] = []
        self.diff_set: set[tuple[Symbol, Symbol]] = set()
        self.float: list[tuple[Type, Symbol]] = []
        self.float_map: dict[Symbol, Label] = {}
        self.essentials: list[list[Symbol]] = []
        self.essentail_map: dict[tuple[Symbol, ...], Label] = {}
        # Note: both self.e and self.e_labels are needed since the keys of
        # self.e_labels form a set, but the order and repetitions of self.e
        # are needed.


class FrameStack(list[Frame]):
    """Class of frame stacks, which extends lists (considered and used as
    stacks).
    """

    def push(self) -> None:
        """Push an empty frame to the stack."""
        self.append(Frame())

    def add_c(self, tok: Symbol) -> None:
        frame = self[-1]
        frame.constants.add(tok)

    def add_v(self, tok: Symbol) -> None:
        frame = self[-1]
        frame.variables.add(tok)

    def add_f(self, label: Symbol, type: Symbol, value: Symbol) -> None:
        frame = self[-1]
        frame.float.append((type, value))
        frame.float_map[value] = label

    def add_e(self, label: Label, type: Symbol, stmt: list[Symbol]) -> None:
        """Add an essential hypothesis (token tuple) to the frame stack
        top.
        """
        frame = self[-1]
        frame.essentials.append(stmt)
        frame.essentail_map[tuple(stmt)] = label
        # conversion to tuple since dictionary keys must be hashable

    def add_d(self, varlist: list[Symbol]) -> None:
        """Add a disjoint variable condition (ordered pair of variables) to
        the frame stack top.
        """
        self[-1].diffs.append(varlist)
        self[-1].diff_set.update(
            (min(x, y), max(x, y))
            for x, y in itertools.product(varlist, varlist)
            if x != y
        )

    def lookup_v(self, tok: Symbol) -> bool:
        """Return whether the given token is an active variable."""
        return any(tok in fr.variables for fr in self)

    def lookup_d(self, x: Symbol, y: Symbol) -> bool:
        """Return whether the given ordered pair of tokens belongs to an
        active disjoint variable statement.
        """
        return any((min(x, y), max(x, y)) in fr.diff_set for fr in self)

    def lookup_f(self, var: Symbol) -> typing.Optional[Label]:
        """Return the label of the active floating hypothesis which types the
        given variable.
        """
        for frame in self:
            try:
                return frame.float_map[var]
            except KeyError:
                pass
        return None  # Variable is not actively typed

    def lookup_e(self, stmt: list[Symbol]) -> typing.Optional[Label]:
        """Return the label of the (earliest) active essential hypothesis with
        the given statement.
        """
        stmt_t = tuple(stmt)
        for frame in self:
            try:
                return frame.essentail_map[stmt_t]
            except KeyError:
                pass
        return None

    def find_vars(self, stmt: list[Symbol]) -> set[Symbol]:
        """Return the set of variables in the given statement."""
        return {x for x in stmt if self.lookup_v(x)}

    def make_assertion(
        self,
        stmt: list[Symbol],
        grammar: Grammar | None,
        types: set[str],
    ):
        """Return a quadruple (disjoint variable conditions, floating
        hypotheses, essential hypotheses, conclusion) describing the given
        assertion.
        """
        e_hyps = [eh for fr in self for eh in fr.essentials]
        mand_vars = {
            tok
            for hyp in itertools.chain(e_hyps, [stmt])
            for tok in hyp
            if self.lookup_v(tok)
        }
        dvs = {
            (x, y)
            for fr in self
            for (x, y) in fr.diff_set
            if x in mand_vars and y in mand_vars
        }
        f_hyps = []
        for fr in self:
            for f_type, f_value in fr.float:
                if f_value in mand_vars:
                    f_hyps.append((f_type, f_value))
                    mand_vars.remove(f_value)
        """
        other props for follow
        """
        f_map = {f_value: f_type for f_type, f_value in f_hyps}
        arguments = []
        for hyp in itertools.chain([stmt], e_hyps):
            for tok in hyp:
                if tok in f_map and tok not in arguments:
                    arguments.append(tok)
        type_idx_record = {}
        argument_map = {}  # (value, alias)
        for f_value in arguments:
            f_type = f_map[f_value]
            if f_type in type_idx_record:
                argument_map[f_value] = "v" + f_type[0] + str(type_idx_record[f_type])
                type_idx_record[f_type] += 1
            else:
                argument_map[f_value] = "v" + f_type[0] + str(0)
                type_idx_record[f_type] = 1

        diffs_list = []
        for fr in self:
            for l in fr.diffs:
                dvs = [v for v in l if v in f_map]
                if dvs not in diffs_list:
                    diffs_list.append(dvs)

        f_labels = [self.lookup_f(f_value) for _, f_value in f_hyps]
        e_labels = [self.lookup_e(stmt) for stmt in e_hyps]

        toks = set(argument_map.values())
        for tok in stmt:
            if tok not in argument_map:
                toks.add(tok)
        for e in e_hyps:
            for tok in e:
                if tok not in argument_map:
                    toks.add(tok)

        stmt_parser = None
        try:
            stmt_parser = grammar.generate_parser(toks)
        except Exception as e:
            print("generate parse error: ", {e})
            stmt_parser = None

        ext_e_hyps = (
            [parse_stmt(e, argument_map, stmt_parser, types) for e in e_hyps]
            if stmt_parser
            else None
        )
        ext_stmt = (
            parse_stmt(stmt, argument_map, stmt_parser, types) if stmt_parser else None
        )

        assertion = dvs, f_hyps, e_hyps, stmt
        extension = (
            diffs_list,
            arguments,
            f_map,  # (value, type)
            argument_map,  # (value, alias)
            f_labels,
            e_labels,
            ext_e_hyps,
            ext_stmt,
        )
        return assertion, extension


def parse_stmt(
    stmt: list[Symbol],
    argument_map: dict[Symbol, str],
    stmt_parser: Lark,
    types: set[str],
):
    reverse_argument_map = {v: k for k, v in argument_map.items()}
    stmt2 = [argument_map.get(tok, tok) for tok in stmt]
    tree = stmt_parser.parse(" ".join(stmt2))
    return [reverse_argument_map.get(tok, tok) for tok in tree_functional(tree, types)]


def tree_functional(tree: Tree, ignores: set[str]):
    ignores = set(ignores)
    ignores.add("start")
    if not isinstance(tree, Tree):
        return
    if tree.data.value in ignores:
        yield from tree_functional(tree.children[0], ignores)
        return
    if len(tree.children) > 0:
        yield decode_label(tree.data.value)
        yield "("
        for idx, child in enumerate(tree.children):
            if idx > 0:
                yield ","
            yield from tree_functional(child, ignores)
        yield ")"
    else:
        yield decode_label(tree.data.value)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="""Translate from metamath to follow
    Example:
        '$ python3 translator.py <source_file> <output_folder>'
    """
    )
    parser.add_argument(
        "-s",
        "--source-file",
        dest="source_file",
        type=str,
        help="""metamath source file""",
    )
    parser.add_argument(
        "-o",
        "--output-folder",
        dest="output_folder",
        type=str,
        default="output",
        help="""output folder""",
    )
    args = parser.parse_args()
    source_file = args.source_file  # 修改这一行
    output_folder = args.output_folder

    path = os.path.join(output_folder)
    if not os.path.exists(path):
        os.makedirs(path)

    follow_folder = os.path.join(path, "code")
    if not os.path.exists(follow_folder):
        os.makedirs(follow_folder)

    json_folder = os.path.join(path, "json")
    if not os.path.exists(json_folder):
        os.makedirs(json_folder)

    with open(source_file, "r") as f:
        grammar = Grammar(f)

    is_first = True

    follow_config_f = open(os.path.join(follow_folder, "content.follow.json"), "w")
    follow_config_f.write('{"content":[')

    json_config_f = open(os.path.join(json_folder, "content.follow.json"), "w")
    json_config_f.write('{"content":[')

    idx = 1

    with open(source_file, "r") as f:
        for filename, content, trajectory in transform(f, grammar):
            print(f"{idx}: {filename}")
            with open(os.path.join(follow_folder, filename + ".fol"), "w") as f_out:
                f_out.write(content)
            with open(os.path.join(json_folder, filename + ".json"), "w") as f_out:
                f_out.write(trajectory)
            if is_first:
                follow_config_f.write(f'"{filename}.fol"')
                json_config_f.write(f'"{filename}.json"')
                is_first = False
            else:
                follow_config_f.write(f',"{filename}.fol"')
                json_config_f.write(f',"{filename}.json"')
            idx += 1
    follow_config_f.write("]}")
    json_config_f.write("]}")
    follow_config_f.close()
    json_config_f.close()
    print("follow_config_f close")
    print("json_config_f close")
