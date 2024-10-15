import os

from metamath_to_follow.generate_grammar import Grammar
from metamath_to_follow.translator import scan, transform


def test_translator_scan():
    path = os.path.join(os.path.dirname(__file__), "../tests/set.mm")  # 更新为相对路径
    with open(path, "r") as f:
        for btype, props in scan(f):
            print(btype, props)
    assert True


def test_translator_transform():
    path = os.path.join(os.path.dirname(__file__), "../tests/set.mm")  # 更新为相对路径
    with open(path, "r") as f:
        grammar = Grammar(f)

    with open(path, "r") as f:
        idx = 0
        for filename, content, trajectory, train_data in transform(f, grammar):
            print(f"{idx}: {filename}")
            idx += 1
    assert True
