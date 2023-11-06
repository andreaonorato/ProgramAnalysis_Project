from filereader import find_method
import z3
from pathlib import Path
from utils import Bytecode, ConcolicValue, State


class Concolic:
    def __init__(self, target) -> None:
        self.solver = z3.Solver()
        self.params = [z3.Int(f"p{i}") for i, _ in enumerate(target["params"])]
        self.bytecode = [Bytecode(b) for b in target["code"]["bytecode"]]

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
                    k: ConcolicValue(i, p)
                    for k, (i, p) in enumerate(zip(input, self.params))
                },
                [],
            )

            pc = 0
            path = []

            for _ in range(k):
                bc = self.bytecode[pc]
                print(pc)
                pc += 1
                print(state)
                print(bc)
                print(path)
                print("---------")

                match bc.opr:
                    case "get":
                        if bc.field["name"] == "$assertionsDisabled":
                            state.push(ConcolicValue.from_const(False))
                        else:
                            raise Exception(f"Unsupported bytecode: {bc}")

                    case "ifz":
                        v = state.pop()
                        z = ConcolicValue.from_const(0)
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
                        state.push(ConcolicValue.from_const(bc.value["value"]))

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
                        state.push(v.binary("add", ConcolicValue.from_const(bc.amount)))
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
                                    getattr(return_concolic.symbolic, "__lt__")(
                                        output_range
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

                            raise Exception(
                                f"Found out of range output eg: {list(zip(self.params,input))}"
                            )
                        result = f"returned {return_concolic}"
                        break

                    case "if":
                        v2 = state.pop()
                        v1 = state.pop()
                        z = ConcolicValue.from_const(0)
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


c = Concolic(find_method(("example_analysis", "calculateEfficiency")))
c.run(z3.IntVal(0))
