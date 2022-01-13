from typing import Any
from parser import *
from proof import *


class Func:
    def __init__(self, eval, prove) -> None:
        self.f = eval
        self.p = prove

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

    proofMatch = False
    for sp in size.proofs:
        for ip in index.proofs:
            if sp == ip:
                proofMatch = True

    assert proofMatch

    return ObjProofs([], {})

def affirmEqToLt(args):
    varProofs: ObjProofs = args[1]

    transformed: List[Proof] = []
    for p in getEqs(varProofs.proofs):
        transformed.append(Proof(Relation.LT, ProofExpr.newPlus(p.expr, ProofExpr.newNumVal(1)).simplify()))

    varProofs.proofs.extend(transformed)

def affirmLtToLtPlusN(args):
    varProofs: ObjProofs = args[1]
    numProofs: ObjProofs = args[2]

    ltAny = Proof(Relation.LT, ProofExpr.newAny())
    ltProofs = filter(lambda x: ltAny.match(x), varProofs.proofs)

    eqNum = Proof(Relation.EQ, ProofExpr.newNumVal(None))
    numProof = next(filter(lambda x: eqNum.match(x), numProofs.proofs), None)

    assert numProof is not None
    numExpr = numProof.expr

    transformed: List[Proof] = []
    for p in ltProofs:
        transformed.append(Proof(Relation.LT, ProofExpr.newPlus(p.expr, numExpr).simplify()))

    varProofs.proofs.extend(transformed)

StdLib = {
    "add": Func(lambda x: x[1] + x[2], addProve),
    "sub": Func(lambda x: x[1] - x[2], subProve),
    "newArray": Func(lambda x: Obj("array", [0]*x[1], {"size": x[1]}), lambda x: ObjProofs([], {"size": x[1]})),
    "getField": Func(lambda x: x[1].getField(x[2]), lambda x: x[1].fieldProofs[x]),
    "getArrayElement": Func(lambda x: x[1].getVal()[x[2]], lambda _: ObjProofs([], {})),
    "setArrayElement": Func(setArrayFunc, setArrayProve),
    "affirmEqToLt": Func(lambda _: None, affirmEqToLt),
    "affirmLtToLtPlusN": Func(lambda _: None, affirmLtToLtPlusN)
}
