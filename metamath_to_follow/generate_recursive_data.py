import itertools
import json
import os

global_vars = set()
for t in ["wff", "setvar", "class"]:
    for idx in range(200):
        global_vars.add(f"g{t[0]}{idx}")
        global_vars.add(f"v{t[0]}{idx}")


def read_block(label, base):
    with open(os.path.join(base, label + ".json"), "r") as f:
        block = json.load(f)
    return block


def translate_operators(label, input_args, base):
    label_info = read_block(label, base)
    arg_map: dict[str, str] = {}
    for idx, (_, a_name) in enumerate(label_info["args"]):
        a_input = input_args[idx]
        arg_map[a_name] = a_input
    if label_info["type"] == "axiom":
        return get_axiom_train_data(label_info, arg_map)
    return get_thm_train_data(label_info, arg_map)


def stmt_subs(targets, conditions, dvs, arg_map):
    new_targets = [
        " ".join([arg_map.get(word, word) for word in ehyp.split(" ")])
        for ehyp in targets
    ]
    new_conditions = [
        " ".join([arg_map.get(word, word) for word in ehyp.split(" ")])
        for ehyp in conditions
    ]
    new_diffs = set()
    if len(dvs) > 0:
        arg_value_map = {
            k: set([word for word in expr.split(" ") if word in global_vars])
            for k, expr in arg_map.items()
        }
        for v1, v2 in dvs:
            v1set = arg_value_map.get(v1)
            v2set = arg_value_map.get(v2)
            for x, y in itertools.product(v1set, v2set):
                new_diffs.add((min(x, y), max(x, y)))
    return new_targets, new_conditions, new_diffs


def get_block_train_data(targets, conditions, dvs, tails=[]):
    rst = []
    for target in targets:
        rst.append("|- " + target)
    for condition in conditions:
        rst.append("-| " + condition)
    if dvs and len(dvs) > 0:
        rst.append("diff")
        for dv in dvs:
            rst.append(" ".join(["(", dv[0], ",", dv[1], ")"]))
    rst += tails
    rst.append("<end>")
    return " ".join(rst)


def get_axiom_train_data(axiom, arg_map):
    new_targets, new_conditions, new_diffs = stmt_subs(
        axiom["targets"], axiom["conditions"], axiom["dvs"], arg_map
    )
    rst = get_block_train_data(new_targets, new_conditions, new_diffs)
    rst += " <qed>"
    return [rst]


def get_thm_train_data(thm, arg_map):
    new_targets, new_conditions, new_diffs = stmt_subs(
        thm["targets"], thm["conditions"], thm["dvs"], arg_map
    )
    tails = []
    for condition in new_conditions:
        tails.append("-| " + condition)

    if len(new_diffs) > 0:
        tails.append("diff")
        for dv in new_diffs:
            tails.append(f"( {dv[0]} , {dv[1]} )")

    states = thm["states"]
    actions = thm["actions"]

    new_states = [get_block_train_data(new_targets, [], [], tails)]

    memories = []
    for idx in range(len(actions)):
        new_state_tokens = new_states[idx]

        a_targets, a_conditions, a_dvs = actions[idx]
        new_a_targets, new_a_conditions, new_a_dvs = stmt_subs(
            a_targets, a_conditions, a_dvs, arg_map
        )
        action_tokens = get_block_train_data(new_a_targets, new_a_conditions, new_a_dvs)

        next_state = states[idx + 1]
        if len(next_state) > 0:
            new_next_state, _, _ = stmt_subs(next_state, [], [], arg_map)
            new_next_state_tokens = get_block_train_data(new_next_state, [], [], tails)
            memories.append(
                " ".join([new_state_tokens, action_tokens, new_next_state_tokens])
            )
            new_states.append(new_next_state_tokens)
        else:
            memories.append(" ".join([new_state_tokens, action_tokens, "<qed>"]))
            new_states.append([])
    return memories
