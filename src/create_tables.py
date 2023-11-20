# FIRST LINE OF THE MAIN
# find_method("FileName","MethodName")
import time
import z3
from concolic import Concolic
import statistics
import csv
from utils import find_method


test_data = [
    (("../data/example_loop.json", "ShowBalance"), [("__ne__", z3.IntVal(0))]),
    (
        ("../data/TestLong.json", "test"),
        [("__ge__", z3.IntVal(-1))],
    ),
    # (("../data/example_NoOutOfRange.json", "ShowBalance"), [("__ne__", z3.IntVal(0))]),
    (
        ("../data/longexample_outofrange.json", "ShowBalance"),
        [("__ne__", z3.IntVal(0))],
    ),
]


for (path, method), limits in test_data:
    c = Concolic(find_method(path, method))
    for skip_loops in [True, False]:
        for i in range(100):
            execution_time = []
            start_time = time.time()
            out_of_range, inputs = c.run(limits, skip_loops, k=20000)

            run_time = time.time() - start_time
            if not out_of_range:
                print("FAIL")
                break
            execution_time.append(run_time)

            print(run_time, out_of_range, inputs)

        stdev = statistics.pstdev(execution_time)
        mean = statistics.mean(execution_time)
        with open("concolic_results.csv", "a", newline="") as r:
            writer = csv.writer(r, delimiter=",")
            writer.writerow([path + method, skip_loops, mean, stdev])
