from typing import Any
from parser import *
from proof import *


class Func:
    def __init__(self, f, p) -> None:
        self.f = f
        self.p = p

    def eval(self, scope: EvalScope, *args):
        return self.f((scope,) + args)

    def prove(self, scope: ProofScope, *args):
        return self.p((scope,) + args)

def addProve(args):
    lhs: ObjProofs = args[1]
    rhs: ObjProofs = args[2]

    results = []
    for left in lhs.proofs:
        for right in rhs.proofs:
            if right.relation == Relation.EQ:
                results.append(Proof(left.relation, ProofExpr.newPlus(left.expr, right.expr).simplify()))

    return ObjProofs(results, {})

def subProve(args):
    lhs: ObjProofs = args[1]
    rhs: ObjProofs = args[2]

    results: List[Proof] = []
    for left in lhs.proofs:
        for right in rhs.proofs:
            if right.relation == Relation.EQ:
                results.append(Proof(left.relation, ProofExpr.newPlus(left.expr, right.expr).simplify()))

    return ObjProofs(results, {})

def newArrayProve(args):
    sizeArgProofs: ObjProofs = args[1]
    return ObjProofs([], {"size": sizeArgProofs})

StdLib = {
    "add": Func(lambda x: x[1] + x[2], addProve),
    "sub": Func(lambda x: x[1] - x[2], subProve),
    "newArray": Func(lambda x: Obj("array", [0]*x[1], {"size": x[1]}), lambda x: ObjProofs([], {"size": x[1]})),
    "getField": Func(lambda x: x[1].getField(x[2]), lambda x: x[1].fieldProofs[x])
}
