# FIRST LINE OF THE MAIN
# find_method("FileName","MethodName")
import time
import z3
from concolic import Concolic

from utils import find_method


test_data = [
    # (("../data/example_loop.json", "ShowBalance"), [("__ne__", z3.IntVal(0))]),
    # (
    #     ("../data/example_analysis.json", "calculateEfficiency"),
    #     [("__ge__", z3.IntVal(0))],
    # ),
    (("../data/example_NoOutOfRange.json", "ShowBalance"), [("__ne__", z3.IntVal(0))]),
]

for (path, method), limits in test_data:
    c = Concolic(find_method(path, method))
    for skip_loops in [True, False]:
        for i in range(2):
            start_time = time.time()
            out_of_range, inputs = c.run(limits, skip_loops=skip_loops, k=200)
            run_time = time.time() - start_time
            print(run_time, out_of_range, inputs)


# we want an output greater than 0, so __ge__
# c = Concolic(find_method("../data/example_analysis.json", "calculateEfficiency"))
# c.run([("__ge__", z3.IntVal(0)), ("__lt__", z3.IntVal(100))], False)

# c = Concolic(find_method("../data/example_NoOutOfRange.json", "ShowBalance"))
# c.run([("__ne__", z3.IntVal(0))])
