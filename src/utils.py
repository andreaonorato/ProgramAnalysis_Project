import z3
import json
from dataclasses import dataclass


@dataclass
class ConcolicValue:
    concrete: int | bool
    symbolic: z3.ExprRef
    name: z3.ExprRef

    def __repr__(self):
        return f"{self.concrete} ({self.symbolic})  name: {self.name}"

    @classmethod
    def from_const(cls, c, pc):
        if isinstance(c, bool):
            return ConcolicValue(c, z3.BoolVal(c), z3.Bool(f"b{pc}"))
        if isinstance(c, int):
            return ConcolicValue(c, z3.IntVal(c), z3.Int(f"i{pc}"))
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
                    z3.simplify(self.name / other.name),
                )

            raise Exception(f"Unknown binary operation: {operant}")

        return ConcolicValue(
            getattr(self.concrete, opr)(other.concrete),
            z3.simplify(getattr(self.symbolic, opr)(other.symbolic)),
            z3.simplify(getattr(self.name, opr)(other.name)),
        )

    def compare(self, copr, other):
        DICT = {"ne": "__ne__", "gt": "__gt__", "ge": "__ge__", "le": "__le__"}
        if copr in DICT:
            opr = DICT[copr]

        else:
            raise Exception(f"Unknown compartition: {copr}")
        return ConcolicValue(
            getattr(self.concrete, opr)(other.concrete),
            z3.simplify(getattr(self.symbolic, opr)(other.symbolic)),
            z3.simplify(getattr(self.name, opr)(other.name)),
        )


@dataclass
class State:
    locals: dict[int, ConcolicValue]
    stack: list[ConcolicValue]

    def push(self, value):
        self.stack.append(value)

    def pop(self):
        return self.stack.pop()

    def load(self, index):
        self.push(self.locals[index])

    def store(self, index):
        self.locals[index] = self.stack.pop()

    def copy(self):
        return State(self.locals.copy(), self.stack.copy())

    def diff(self, otherState):
        locals_diff = {}
        for i, local in self.locals.items():
            locals_diff[i] = local.binary("sub", otherState.locals[i])
        stack_diff = []
        for i, s in enumerate(self.stack):
            stack_diff.append(s.binary("sub", otherState.stack[i]))
        return State(locals_diff, stack_diff)

    def skipLoop(self, diffState, iterations):
        for i, local in self.locals.items():
            self.locals[i] = local.binary(
                "add", diffState.locals[i].binary("mul", iterations)
            )
        for i, s in enumerate(self.stack):
            self.stack[i] = s.binary(
                "add", diffState.stack[i].binary("mul", iterations)
            )

    def findDelta(states, variable):
        return states[-1].diff(states[-2])


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


import numpy as np
from sklearn.linear_model import LinearRegression


def linearRegression(x_values, y_values, iterations):
    # Reshape the input variable to a 2D array
    x_values = np.reshape(x_values, (-1, 1))

    # Create a linear regression model and fit the data
    model = LinearRegression()
    model.fit(x_values, y_values)
    expr = z3.IntVal(model.intercept_)
    for i, coef in enumerate(model.coef_):
        expr = expr + coef * iterations ** (i + 1)
    return expr


def predict_iterations_if(stateMap, pc, operator, negative):
    x_values = [state.stack[0].concrete for state in stateMap[pc]]
    x2_values = [state.stack[1].concrete for state in stateMap[pc]]
    y_values = list(range(0, len(stateMap[pc])))
    iterations = z3.Int(f"x{pc}")
    f1 = linearRegression(x_values, y_values, iterations)
    f2 = linearRegression(x2_values, y_values, iterations)
    loop_solver = z3.Solver()

    expr = getattr(f1, operator)(f2)
    if negative:
        expr = expr = z3.Not(expr)
    loop_solver.add(
        z3.And(
            iterations > 0,
            expr,
        )
    )
    if loop_solver.check() == z3.sat:
        m = loop_solver.model()
        return m[iterations].as_long()
    else:
        return -1
