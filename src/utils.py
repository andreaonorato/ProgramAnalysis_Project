import z3
import json
from dataclasses import dataclass


@dataclass
class ConcolicValue:
    concrete: int | bool
    symbolic: z3.ExprRef

    def __repr__(self):
        return f"{self.concrete} ({self.symbolic})"

    @classmethod
    def from_const(cls, c):
        if isinstance(c, bool):
            return ConcolicValue(c, z3.BoolVal(c))
        if isinstance(c, int):
            return ConcolicValue(c, z3.IntVal(c))
        raise Exception(f"Unknown const: {c}")

    def binary(self, operant, other):
        DICT = {"sub": "__sub__", "add": "__add__", "mul": "__mul__"}

        if operant in DICT:
            opr = DICT[operant]

        else:
            if operant == "div":
                return ConcolicValue(
                    self.concrete // other.concrete,
                    z3.simplify(self.symbolic / other.symbolic),
                )

            raise Exception(f"Unknown binary operation: {operant}")

        return ConcolicValue(
            getattr(self.concrete, opr)(other.concrete),
            z3.simplify(getattr(self.symbolic, opr)(other.symbolic)),
        )

    def compare(self, copr, other):
        # ne = not equal, gt = greater than, ge = greater than or equal, le = less than or equal
        # we are missing less than (lss)
        DICT = {"ne": "__ne__", "gt": "__gt__", "ge": "__ge__", "le": "__le__"}
        if copr in DICT:
            opr = DICT[copr]

        else:
            raise Exception(f"Unknown compartition: {copr}")
        return ConcolicValue(
            getattr(self.concrete, opr)(other.concrete),
            z3.simplify(getattr(self.symbolic, opr)(other.symbolic)),
        )


@dataclass
class State:
    # locals 1 p0, 2p1, 10 p4*p1
    locals: dict[int, ConcolicValue]
    # stack where we push values
    stack: list[ConcolicValue]

    def push(self, value):
        self.stack.append(value)

    def pop(self):
        return self.stack.pop()

    def load(self, index):
        # push the operation on the stack
        self.push(self.locals[index])

    def store(self, index):
        # take from the stack 
        self.locals[index] = self.stack.pop()

    def copy(self):
        #copy the state so there are no problems with by pointer passages
        return State(self.locals.copy(), self.stack.copy())
    #takes 2 states and returns 1 state
    def diff(self, otherState):
        locals_diff = {}
        for i, local in self.locals.items():
            locals_diff[i] = local.binary("sub", otherState.locals[i])
        stack_diff = []
        for i, s in enumerate(self.stack):
            stack_diff.append(s.binary("sub", otherState.stack[i]))
        return State(locals_diff, stack_diff)
    # not implemented
    def skipLoop(self, diffState, iterations):
        for i, local in self.locals.items():
            self.locals[i] = local.binary(
                "add", diffState.locals[i].binary("mul", iterations)
            )
        for i, s in enumerate(self.stack):
            self.stack[i] = s.binary(
                "add", diffState.stack[i].binary("mul", iterations)
            )


@dataclass
class Bytecode:
    dictionary: dict

    def __getattr__(self, name):
        return self.dictionary[name]

    def __repr__(self):
        return f"{self.opr} " + " ".join(
            f"{k}: {v}"
            for k, v in self.dictionary.items()
            if k != "opr" and k != "offset"
        )
