from filereader import find_method
import z3
import time
from pathlib import Path
from utils import Bytecode, ConcolicValue, State


class Concolic:

    #this is the object, returns None
    def __init__(self, target) -> None:
        # one of the parameters is z3.solver
        self.solver = z3.Solver()
        # this is a list of the parameters (inputs) of the analyzed function
        self.params = [z3.Int(f"p{i}") for i, _ in enumerate(target["params"])]
        # what are you doing to the bytecode?
        self.bytecode = [Bytecode(b) for b in target["code"]["bytecode"]]
        # map of the state one where we are
        self.stateMap = {}
    # output_range = ("__ne__", z3.IntVal(0))
    def run(self, output_range, k=1000):
        # print(bytecode)
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
                    k: ConcolicValue(i, p)
                    for k, (i, p) in enumerate(zip(input, self.params))
                },
                [],
            )
            # print("This is the state: ",state)
            # K is the depth
            pc = 0
            path = []

            for _ in range(k):
                if pc not in self.stateMap.keys():
                    self.stateMap[pc] = [] # create the space for the variables for that pc
                self.stateMap[pc].append(state.copy())
                bc = self.bytecode[pc] #take only the operation line like load, add, etc
                print(pc)
                print(state, "\n")
                print(bc, "\n" )
                print(path)
                pc += 1
                
                match bc.opr:
                    
                    case "get":
                        if bc.field["name"] == "$assertionsDisabled":
                            state.push(ConcolicValue.from_const(False))
                        else:
                            raise Exception(f"Unsupported bytecode: {bc}")

                    case "ifz":
                        v = state.pop()                 # take the state
                        z = ConcolicValue.from_const(0) # z3.intvalue(0)
                        r = ConcolicValue.compare(v, bc.condition, z) #bc.condition like gt ne...
                        if r.concrete:
                            pc = bc.target # target of where to go
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
                                f"Found out of range output {invalid_output} for inputs: {list(zip(self.params,input))} in {time.time()-start_time} seconds"
                                
                            )
                        result = f"returned {return_concolic}"
                        break

                    case "if":
                        if len(self.stateMap[pc - 1]) > 1:
                            state_difference = state.diff(self.stateMap[pc - 1][0])
                            self.stateMap[pc - 1] = []
                            v2_delta = state_difference.pop()
                            v1_delta = state_difference.pop()
                            v2 = state.pop()
                            v1 = state.pop()
                            loop_solver = z3.Solver()
                            iterations = z3.Int("x")
                            loop_solver.add(
                                z3.And(
                                    iterations >= 0,
                                    v1.symbolic + v1_delta.symbolic * iterations
                                    >= v2.symbolic + v2_delta.symbolic * iterations,
                                )
                            )
                            loop_solver.check()
                            m = loop_solver.model()
                            state.skipLoop(
                                state_difference,
                                ConcolicValue.from_const(m[iterations].as_long()),
                            )
                            pc = bc.target
                        else:
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


# c = Concolic(find_method(("example_loop", "ShowBalance")))
# c.run(("__ne__", z3.IntVal(0)))

# c = Concolic(find_method(("example_analysis", "calculateEfficiency")))
# c.run(("__ge__", z3.IntVal(0)))
# FIRST LINE OF THE MAIN
#find_method("FileName","MethodName")
start_time = time.time()
c = Concolic(find_method(("example_loop", "ShowBalance")))
# c = Concolic(find_method(("example_NoOutOfRange", "ShowBalance")))
#c = Concolic(find_method(("example_analysis", "calculateEfficiency")))

# z3.IntVal(0) it's like a normal 0 used by z3
# we want an output greater than 0, so __ge__
c.run(("__ne__", z3.IntVal(0)))   # To test example_loop or example_NoOutOfRange
# c.run(("__ge__", z3.IntVal(0)))   # To test example_analysis
