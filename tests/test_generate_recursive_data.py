import json
import os

from metamath_to_follow.generate_recursive_data import translate_operators


def test_generate_recursive_data():
    base = os.path.join(
        os.path.dirname(__file__), "./follow/set.mm/json"
    )  # 更新为相对路径
    thmname = "undisj1"

    with open(os.path.join(base, thmname + ".json"), "r") as f:
        thm = json.load(f)

    for label, input_args in thm["operators"]:
        memory = translate_operators(
            label, input_args, base="./tests/follow/set.mm/json"
        )
        assert len(memory) > 0
