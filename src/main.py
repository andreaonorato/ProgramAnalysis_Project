from filereader import find_method
import z3
from pathlib import Path
from utils import Bytecode, ConcolicValue, State


class Concolic:
    def __init__(self, target) -> None:
        self.solver = z3.Solver()
        self.params = [z3.Int(f"p{i}") for i, _ in enumerate(target["params"])]
        self.bytecode = [Bytecode(b) for b in target["code"]["bytecode"]]
        self.stateMap = {}
        self.skipLoop = {}

    def getLowestSkipLoop(self):
        skip = -1
        for k, v in self.skipLoop.items():
            if skip == -1:
                skip = v
            elif skip > v:
                skip = v
        return skip

    # make this function consider path until there in loop
    def iterationsUntilNot(self, state, pc, bc):
        state_difference = state.diff(self.stateMap[pc][0])

        v2_delta = state_difference.stack[-1]
        v1_delta = state_difference.stack[-2]
        v2 = state.stack[-1]
        v1 = state.stack[-2]
        loop_solver = z3.Solver()
        iterations = z3.Int("x")
        loop_solver.add(
            z3.And(
                iterations >= 0,
                v1.symbolic + v1_delta.symbolic * iterations
                >= v2.symbolic + v2_delta.symbolic * iterations,
            )
        )
        if loop_solver.check() == z3.sat:
            m = loop_solver.model()
            return m[iterations].as_long()
        return -1

    def run(self, output_range, k=1000):
        # print(bytecode)

        while self.solver.check() == z3.sat:
            model = self.solver.model()
            input = [
                model.eval(p, model_completion=True).as_long() for p in self.params
            ]
            print(input)

            state = State(
                {
                    k: ConcolicValue(i, p, p)
                    for k, (i, p) in enumerate(zip(input, self.params))
                },
                [],
            )

            pc = 0
            path = []

            for _ in range(k):
                if pc not in self.stateMap.keys():
                    self.stateMap[pc] = []

                self.stateMap[pc].append(state.copy())
                bc = self.bytecode[pc]
                print("---------")
                print(pc)
                print(state)
                print(bc)
                print(path)

                pc += 1

                match bc.opr:
                    case "get":
                        if bc.field["name"] == "$assertionsDisabled":
                            state.push(ConcolicValue.from_const(False, pc - 1))
                        else:
                            raise Exception(f"Unsupported bytecode: {bc}")

                    case "ifz":
                        v = state.pop()
                        z = ConcolicValue.from_const(0, pc - 1)
                        r = ConcolicValue.compare(v, bc.condition, z)
                        if r.concrete:
                            pc = bc.target
                            path += [r.symbolic]
                        else:
                            print("false")
                            path += [z3.simplify(z3.Not(r.symbolic))]
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
                        check_return.add(
                            z3.simplify(
                                z3.And(
                                    *path,
                                    z3.Not(
                                        getattr(
                                            return_concolic.symbolic, output_range[0]
                                        )(output_range[1])
                                    ),
                                )
                            )
                        )
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
                                f"Found out of range output {invalid_output} for inputs: {list(zip(self.params,input))}"
                            )
                        result = f"returned {return_concolic}"
                        break

                    case "if":
                        if pc - 1 in self.skipLoop.keys():
                            skipIterations = self.getLowestSkipLoop()
                            if skipIterations == -1:
                                raise Exception(f"Loop will not finish")
                            state.skipLoop(
                                state.diff(self.stateMap[pc - 1][0]),
                                ConcolicValue.from_const(skipIterations, pc - 1),
                            )

                            for k in range(pc - 1, bc.target):
                                if k in self.stateMap.keys():
                                    self.stateMap.pop(k)
                                if k in self.skipLoop.keys():
                                    self.skipLoop.pop(k)

                            pc = pc - 1
                        else:
                            if len(self.stateMap[pc - 1]) > 1:
                                self.skipLoop[pc - 1] = self.iterationsUntilNot(
                                    state, pc - 1, bc
                                )
                            v2 = state.pop()
                            v1 = state.pop()
                            z = ConcolicValue.from_const(0, pc - 1)
                            r = ConcolicValue.compare(v1, bc.condition, v2)

                            if r.concrete:
                                pc = bc.target
                                path += [r.symbolic]
                            else:
                                path += [z3.simplify(z3.Not(r.symbolic))]

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


# c = Concolic(find_method(("example_loop", "ShowBalance")))
# c.run(("__ne__", z3.IntVal(0)))

# c = Concolic(find_method(("example_analysis", "calculateEfficiency")))
# c.run(("__ge__", z3.IntVal(0)))

c = Concolic(find_method(("example_NoOutOfRange", "ShowBalance")))
c.run(("__ne__", z3.IntVal(0)))
