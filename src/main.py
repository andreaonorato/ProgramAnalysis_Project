from filereader import find_method
import z3
import time
from pathlib import Path
from utils import Bytecode, ConcolicValue, State

LOOP_UNTIL_SKIP = 2
MIN_SKIP_SIZE = 3


class Concolic:

    #this is the object, returns None
    def __init__(self, target) -> None:
        # one of the parameters is z3.solver
        self.solver = z3.Solver()
        # this is a list of the parameters (inputs) of the analyzed function
        self.params = [z3.Int(f"p{i}") for i, _ in enumerate(target["params"])]
        self.bytecode = [Bytecode(b) for b in target["code"]["bytecode"]]

    def run(self, output_range, skip_loops=True, k=100):
        # check the satisfability of a set of constrains using z3 solver
        # whille "set of contraints" is satisfiable
        while self.solver.check() == z3.sat:
            model = self.solver.model() # A model in Z3 is an assignment of values to variables that satisfies the given logical conditions.
            input = [
                #list called input with all the values given to the variables to satisfy all the constrains
                model.eval(p, model_completion=True).as_long() for p in self.params
            ]
            #concrete values part of the concolic analysis
            #print("This is my input ",input, "\n\n\n\n\n\n")

            # Each state has a dict and a list
            
            # The dict of the State object is with key-value pairs where the keys are indices and the values are instances of ConcolicValue initialized with values from input and self.params
            # The empty list is the stack, which is empty at the beginning
            # State(locals={0: 1 (p0), 1: 1 (p1), 2: 10 (p2), 3: 10 (p3)}, stack=[])
            # State(locals={$k$: $input_mapped_to_variable$ ($params$), etc, stack=[])
            state = State(
                {
                    k: ConcolicValue(i, p, p)
                    for k, (i, p) in enumerate(zip(input, self.params))
                },
                [],
            )
            # print("This is the state: ",state)
            # K is the depth
            pc = 0
            path = []
            if skip_loops:
                self.stateMap = {}
                self.ifResult = {}
                self.skipLoop = {}
                self.skippedPathExpr = {}
            for _ in range(k):
                if skip_loops:
                    if pc not in self.stateMap.keys():
                        self.stateMap[pc] = []
                        self.ifResult[pc] = []
                    self.stateMap[pc].append(state.copy())

                bc = self.bytecode[pc]
                print("---------")
                print(pc)
                print(state, "\n")
                print(bc, "\n" )
                print(path)

                pc += 1
                
                match bc.opr:
                    
                    case "get":
                        if bc.field["name"] == "$assertionsDisabled":
                            state.push(ConcolicValue.from_const(False, pc - 1))
                        else:
                            raise Exception(f"Unsupported bytecode: {bc}")

                    case "ifz":
                        if skip_loops and pc - 1 in self.skipLoop.keys():
                            state, path = self.skip_iterations(state, pc, bc, path)
                            pc = pc - 1
                        else:
                            if (
                                skip_loops
                                and len(self.stateMap[pc - 1]) > LOOP_UNTIL_SKIP
                            ):
                                self.iterationsUntilNot(state.copy(), pc - 1, bc, True)
                            v = state.pop()
                            z = ConcolicValue.from_const(0, pc - 1)
                            r = ConcolicValue.compare(v, bc.condition, z)
                            if r.concrete:
                                if skip_loops:
                                    self.ifResult[pc - 1].append(True)
                                pc = bc.target
                                path += [r.symbolic]

                            else:
                                path += [z3.simplify(z3.Not(r.symbolic))]
                                if skip_loops:
                                    self.ifResult[pc - 1].append(False)
                    case "load":
                        state.load(bc.index)

                    case "store":
                        state.store(bc.index)

                    case "push":
                        state.push(ConcolicValue.from_const(bc.value["value"], pc - 1))

                    case "binary":
                        v2 = state.pop()
                        v1 = state.pop()

                        if bc.operant == "div":
                            if v2.concrete == 0:
                                result = "Divide by 0"
                                path += [v2.symbolic == 0]
                                break

                            else:
                                path += [z3.simplify(z3.Not(v2.symbolic == 0))]

                        r = v1.binary(bc.operant, v2)
                        state.push(r)

                    case "incr":
                        state.load(bc.index)
                        v = state.pop()
                        state.push(
                            v.binary("add", ConcolicValue.from_const(bc.amount, pc - 1))
                        )
                        state.store(bc.index)

                    case "goto":
                        pc = bc.target

                    case "return":
                        if bc.type is None:
                            result = "return"

                        return_concolic = state.pop()
                        check_return = z3.Solver()
                        range_expr = []
                        for operator, limit in output_range:
                            range_expr.append(
                                z3.Not(
                                    getattr(return_concolic.symbolic, operator)(limit)
                                ),
                            )
                        check_return.add(z3.And(*path, z3.Or(*range_expr)))
                        if check_return.check() == z3.sat:
                            invalid_return = check_return.model()
                            input = [
                                invalid_return.eval(p, model_completion=True).as_long()
                                for p in self.params
                            ]
                            invalid_output = invalid_return.eval(
                                return_concolic.symbolic
                            )

                            raise Exception(
                                f"Found out of range output {invalid_output} for inputs: {list(zip(self.params,input))} in {time.time()-start_time} seconds"
                                
                            )
                        result = f"returned {return_concolic}"
                        break

                    case "if":
                        if skip_loops and pc - 1 in self.skipLoop.keys():
                            state, path = self.skip_iterations(state, pc, bc, path)
                            pc = pc - 1
                        else:
                            if (
                                skip_loops
                                and len(self.stateMap[pc - 1]) > LOOP_UNTIL_SKIP
                            ):
                                self.iterationsUntilNot(state.copy(), pc - 1, bc)
                            v2 = state.pop()
                            v1 = state.pop()
                            r = ConcolicValue.compare(v1, bc.condition, v2)

                            if r.concrete:
                                if skip_loops:
                                    self.ifResult[pc - 1].append(True)
                                pc = bc.target
                                path += [r.symbolic]

                            else:
                                path += [z3.simplify(z3.Not(r.symbolic))]
                                if skip_loops:
                                    self.ifResult[pc - 1].append(False)

                    case "new":
                        if bc.dictionary["class"] == "java/lang/AssertionError":
                            result = "AssertionError"
                            break
                        else:
                            raise Exception(f"Unsupported bytecode: {bc}")

                    case _:
                        raise Exception(f"Unsupported bytecode: {bc}")

            else:
                result = "out of iterations"

            path_constraint = z3.simplify(z3.And(*path))
            print(input, "->", result, "|", path_constraint)

            self.solver.add(z3.Not(path_constraint))
        if not self.solver.check() == z3.sat:
            print("No out of range values")

    def skip_iterations(self, state, pc, bc, path):
        skipIterations = self.getLowestSkipLoop()
        if skipIterations == -1:
            raise Exception(f"Loop will not finish")
        if skipIterations < MIN_SKIP_SIZE:
            skipIterations = 0
        state.skipLoop(
            state.diff(self.stateMap[pc - 1][-2]),
            ConcolicValue.from_const(skipIterations - 1, pc - 1),
        )

        for k in range(pc - 1, bc.target):
            if k in self.skippedPathExpr:
                if self.skipLoop[k] >= skipIterations or self.skipLoop[k] == -1:
                    # works but is shit
                    for i in range(skipIterations):
                        path += [
                            z3.substitute(
                                z3.Not(self.skippedPathExpr[k]),
                                (z3.Int(f"x{k}"), z3.IntVal(i)),
                            ),
                        ]
                self.skippedPathExpr.pop(k)
            if k in self.stateMap.keys():
                self.stateMap.pop(k)
            if k in self.skipLoop.keys():
                self.skipLoop.pop(k)

        return state, path

    def getLowestSkipLoop(self):
        skip = -1
        for k, v in self.skipLoop.items():
            if skip == -1:
                skip = v
            elif skip > v and v > 0:
                skip = v
        return skip

    # make this function consider path until there in loop
    def iterationsUntilNot(self, state, pc, bc, ifz=False):
        negativeTest = False
        constant = True
        if all(self.ifResult[pc]):
            negativeTest = True
        elif all(not r for r in self.ifResult[pc]):
            negativeTest = False
        else:
            constant = False
            self.stateMap = {}
            self.ifResult = {pc: []}
            self.skipLoop = {}
            self.skippedPathExpr = {}
        if constant:
            DICT = {"ne": "__ne__", "gt": "__gt__", "ge": "__ge__", "le": "__le__"}
            if bc.condition in DICT:
                opr = DICT[bc.condition]

            state_difference = state.diff(self.stateMap[pc][-2])

            if not ifz:
                v2_delta = state_difference.pop()
                v2 = state.pop()

            v1_delta = state_difference.pop()
            v1 = state.pop()
            loop_solver = z3.Solver()
            iterations = z3.Int(f"x{pc}")

            if ifz:
                expr = getattr(v1.concrete + v1_delta.concrete * iterations, opr)(0)
                path_expr = getattr(v1.symbolic + v1_delta.symbolic * iterations, opr)(
                    0
                )

            else:
                expr = getattr(v1.concrete + v1_delta.concrete * iterations, opr)(
                    v2.concrete + v2_delta.concrete * iterations
                )
                path_expr = getattr(v1.symbolic + v1_delta.symbolic * iterations, opr)(
                    v2.symbolic + v2_delta.symbolic * iterations
                )

            if negativeTest:
                expr = z3.Not(expr)
                path_expr = z3.Not(path_expr)
            loop_solver.add(
                z3.And(
                    iterations > 0,
                    expr,
                )
            )
            self.skippedPathExpr[pc] = path_expr
            if loop_solver.check() == z3.sat:
                m = loop_solver.model()
                self.skipLoop[pc] = m[iterations].as_long()
            else:
                self.skipLoop[pc] = -1

# FIRST LINE OF THE MAIN
#find_method("FileName","MethodName")
start_time = time.time()
c = Concolic(find_method(("example_loop", "ShowBalance")))
c.run([("__ne__", z3.IntVal(0))], skip_loops=True, k=100)

# we want an output greater than 0, so __ge__
# c = Concolic(find_method(("example_analysis", "calculateEfficiency")))
# c.run([("__ge__", z3.IntVal(0)), ("__lt__", z3.IntVal(100))], False)

# c = Concolic(find_method(("example_NoOutOfRange", "ShowBalance")))
# c.run(("__ne__", z3.IntVal(0)))

