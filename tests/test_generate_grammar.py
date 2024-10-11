import os

from src.generate_grammar import Grammar


def test_generate_grammar():
    path = os.path.join(os.path.dirname(__file__), "../set.mm/set.mm")  # 更新为相对路径
    code = "( vw0 -> vw1 )"
    with open(path, "r") as f:
        grammar = Grammar(f)
        parser = grammar.generate_parser()
        assert parser is not None

    tree = parser.parse(code)
    assert tree is not None
