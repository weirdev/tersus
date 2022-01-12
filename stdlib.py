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

def getEqs(proofs: List[Proof]):
    for p in proofs:
        if p.relation == Relation.EQ:
            yield p

def addProve(args):
    lhs: ObjProofs = args[1]
    rhs: ObjProofs = args[2]

    results = []
    for left in lhs.proofs:
        for right in getEqs(rhs.proofs):
            results.append(Proof(left.relation, ProofExpr.newPlus(left.expr, right.expr).simplify()))

    return ObjProofs(results, {})

def subProve(args):
    lhs: ObjProofs = args[1]
    rhs: ObjProofs = args[2]

    results: List[Proof] = []
    for left in lhs.proofs:
        for right in getEqs(rhs.proofs):
            results.append(Proof(left.relation, ProofExpr.newPlus(left.expr, right.expr).simplify()))

    return ObjProofs(results, {})

def newArrayProve(args):
    sizeArgProofs: ObjProofs = args[1]
    return ObjProofs([], {"size": sizeArgProofs})

def setArrayFunc(args):
    args[1].getVal()[args[2]] = args[3]
    return args[3]

def setArrayProve(args):
    arrObj: ObjProofs = args[1]
    index: ObjProofs = args[2]

    size = arrObj.fieldProofs["size"]

    ltValProof = Proof(Relation.LT, ProofExpr.newNumVal(None))
    
    indexLt = next(filter(lambda x: ltValProof.match(x), index.proofs), None)
    sizeLt = next(filter(lambda x: ltValProof.match(x), size.proofs), None)

    assert indexLt is not None
    assert sizeLt is not None

    assert indexLt.expr.numVal < sizeLt.expr.numVal # TODO: New affirm function proving x < n -> x < n + 1 (or arbitrary positive int)

    return ObjProofs([], {})

def affirmEqToLessThan(args):
    varProofs: ObjProofs = args[1]

    transformed: List[Proof] = []
    for p in getEqs(varProofs.proofs):
        transformed.append(Proof(Relation.LT, ProofExpr.newPlus(p.expr, ProofExpr.newNumVal(1)).simplify()))

    varProofs.proofs.extend(transformed)

StdLib = {
    "add": Func(lambda x: x[1] + x[2], addProve),
    "sub": Func(lambda x: x[1] - x[2], subProve),
    "newArray": Func(lambda x: Obj("array", [0]*x[1], {"size": x[1]}), lambda x: ObjProofs([], {"size": x[1]})),
    "getField": Func(lambda x: x[1].getField(x[2]), lambda x: x[1].fieldProofs[x]),
    "getArrayElement": Func(lambda x: x[1].getVal()[x[2]], lambda _: ObjProofs([], {})),
    "setArrayElement": Func(setArrayFunc, setArrayProve),
    "affirmEqToLessThan": Func(lambda _: None, affirmEqToLessThan)
}
