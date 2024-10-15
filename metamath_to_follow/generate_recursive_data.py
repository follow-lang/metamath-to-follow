import json
import os


def generate_thm_data(label, base="./tests/follow/set.mm/json"):
    with open(os.path.join(base, label + ".json"), "r") as f:
        thm = json.load(f)
    if thm["type"] != "thm":
        return
