import os

from metamath_to_follow.parse_as_book import scan


def test_scan():
    path = os.path.join(os.path.dirname(__file__), "../tests/set.mm")  # 更新为相对路径
    with open(path, "r") as f:
        blocks = list(scan(f))
    assert len(blocks) == 10998
