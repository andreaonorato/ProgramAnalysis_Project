from pathlib import Path
import json
#optimize, open only the file you need. thanks :)


dc = Path("../data/")

classes = {}


#open the jsons and take all the classes names
for f in dc.glob("**/*.json"):
    with open(f) as p:
        doc = json.load(p)
        classes[doc["name"]] = doc #doc is the entire json
## lemme print classes


methods = {}
#classes.vales()-->json1,json2,json3
for cls in classes.values():
    # methods is a list of dicts, where every dict is a method
    for m in cls["methods"]:
        # m is a dict
        # the key is (className,methodName) and the value is the bytecode
        methods[(cls["name"], m["name"])] = m

# am is a tuple, className,methodName
def find_method(am):
    return methods[(am)]


def print_bytecode(am):
    m = find_method(am)
    assert m is not None
    print(m["code"]["bytecode"])


# print_bytecode(("eu/bogoe/dtu/exceptional/Arrays", "dependsOnLattice1"))
