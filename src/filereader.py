from pathlib import Path
import json

dc = Path("../")

classes = {}
for f in dc.glob("**/*.json"):
    with open(f) as p:
        doc = json.load(p)
        classes[doc["name"]] = doc

methods = {}
for cls in classes.values():
    for m in cls["methods"]:
        methods[(cls["name"], m["name"])] = m


def find_method(am):
    return methods[(am)]


def print_bytecode(am):
    m = find_method(am)
    assert m is not None
    print(m["code"]["bytecode"])


# print_bytecode(("eu/bogoe/dtu/exceptional/Arrays", "dependsOnLattice1"))
