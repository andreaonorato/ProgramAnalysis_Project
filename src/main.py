import json 
from filereader7 import find_method 
import z3
from dataclasses import dataclass
from pathlib import Path

@dataclass
class ConcolicValue:
    concrete : int | bool 
    symbolic : z3.ExprRef
    
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
        
        DICT = {
            "sub" : "__sub__",
            "add" : "__add__",
            "mul" : "__mul__"
            
            }
        
        if operant in DICT:
            opr = DICT[operant]
            
            
        else:
            
            if operant == "div":
                return ConcolicValue(
                    self.concrete // other.concrete,
                    z3.simplify(self.symbolic / other.symbolic)
                                     )
                
                
                
            raise Exception(f"Unknown binary operation: {operant}")
        
        return ConcolicValue(
            getattr(self.concrete, opr)(other.concrete),
            z3.simplify(getattr(self.symbolic, opr)(other.symbolic))
                             )
        
    def compare(self, copr, other):
        
        DICT = {
            "ne" : "__ne__",
            "gt" : "__gt__",
            "ge" : "__ge__",
            "le" : "__le__"
            
            
            }
        if copr in DICT:
            opr = DICT[copr]
            
        else:
            raise Exception(f"Unknown compartition: {copr}")
        
        return ConcolicValue(
            getattr(self.concrete, opr)(other.concrete),
            z3.simplify(getattr(self.symbolic, opr)(other.symbolic))
                             )
    
            
        
    
    
    
@dataclass
class State: 
    locals : dict[int, ConcolicValue]
    stack : list[ConcolicValue]
    
    def push(self, value):
        self.stack.append(value)
    
    def pop(self):
        return self.stack.pop()
    
    def load(self, index):
        self.push(self.locals[index])
        
    def store(self, index):
        self.locals[index] = self.stack.pop()
    
    
        

@dataclass
class Bytecode: 
    dictionary : dict 
    
    def __getattr__(self, name):
        return self.dictionary[name]
    
    def __repr__(self):
        return f"{self.opr} " + " ".join(f"{k}: {v}" for k , v in self.dictionary.items() if k != "opr" and k!= "offset")
    


    
target = None 

target = find_method(("dtu/compute/exec/Simple", "factorial"))

 
def concolic(target, k=1000):
    solver = z3.Solver()
    
    params = [z3.Int(f"p{i}") for i, _ in enumerate(target["params"])]
    
    bytecode = [Bytecode(b) for b in target["code"]["bytecode"]]
    print(bytecode)
    
    while solver.check() == z3.sat:
        model = solver.model()
        input = [model.eval(p, model_completion = True).as_long() for p in params]
        print(input)
        
        state = State(
            {k: ConcolicValue(i,p) for k, (i,p) in enumerate(zip(input,params))},
             [],
             )
        
        pc = 0
        path = []
        
        for _ in range(k):
            bc = bytecode[pc]
            pc += 1
# =============================================================================
# 
#             print(state)
#             print(bc)
#             print(path)
#             print("---------")
# =============================================================================

            if bc.opr == "get" and bc.field["name"] == "$assertionsDisabled":
                state.push(ConcolicValue.from_const(False))
            elif bc.opr == "ifz":
                v = state.pop()
                z = ConcolicValue.from_const(0)
                r = ConcolicValue.compare(z, bc.condition, v)
                if r.concrete:
                    pc = bc.target
                    path += [r.symbolic]
                else:
                    path += [z3.simplify(z3.Not(r.symbolic))]
            elif bc.opr == "load":
                state.load(bc.index)
                
            elif bc.opr == "store":
                state.store(bc.index)
                
            elif bc.opr == "push":
                state.push(ConcolicValue.from_const(bc.value["value"]))
            
            elif bc.opr == "binary":
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
                
            elif bc.opr == "incr":
                state.load(bc.index)
                v = state.pop()
                state.push(v.binary("add", ConcolicValue.from_const(bc.amount)))
                state.store(bc.index)
                
            elif bc.opr == "goto":
                pc = bc.target
                
            
            elif bc.opr == "return":
                if bc.type is None:
                    result = "return"
                    
                result = f"returned {state.pop()}"
                break

            
            elif bc.opr == "if":
                v2 = state.pop()
                v1 = state.pop()
                z = ConcolicValue.from_const(0)
                r = ConcolicValue.compare(v1, bc.condition, v2)
                if r.concrete:
                    pc = bc.target
                    path += [r.symbolic]
                else:
                    path += [z3.simplify(z3.Not(r.symbolic))]
                    
            elif bc.opr == "new" and bc.dictionary["class"] == "java/lang/AssertionError":
                    result = "AssertionError" 
                    break
                
            else:
                raise Exception(f"Unsupported bytecode: {bc}")
                
        else: result = "out of iterations"
        
        path_constraint = z3.simplify(z3.And(*path))
        print(input, "->", result, "|",  path_constraint)
        
        solver.add(z3.Not(path_constraint))
   
concolic(target)   
   
#dc = Path("C:/Users/User/Desktop/Program Analysis/course-02242-examples/decompiled/eu/bogoe/dtu/exceptional")

# =============================================================================
# classes = {}
# for f in dc.glob("**/*.json"):
#     with open(f) as p:
#         doc = json.load(p)
#         classes[doc["name"]] = doc
# 
# methods = {}
# for cls in classes.values():
#     for m in cls["methods"]:        
#         methods[(cls["name"],m["name"])] = m
#         
# for target in methods:
#     concolic((m))
#         
# =============================================================================

    
