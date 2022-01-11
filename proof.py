from typing import Dict, List, Optional
from enum import Enum


class Relation(Enum):
    EQ = 1
    GT = 2
    LT = 3
    GTEQ = 4
    LTEQ = 5

class ValType(Enum):
    NUM = 1

class ProofOp(Enum):
    NUMVAL = 1
    PLUS = 2
    MINUS = 3

class ProofExpr:
    def __init__(self, numVal: Optional[int], op: ProofOp, args: List['ProofExpr']) -> None:
        self.numVal = numVal
        self.op = op
        self.args = args

    def simplify(self) -> 'ProofExpr':
        if self.op == ProofOp.NUMVAL:
            return self
        elif self.op == ProofOp.PLUS:
            if self.args[0].op == ProofOp.NUMVAL or self.args[1].op == ProofOp.NUMVAL:
                return ProofExpr.newNumVal(self.args[0].numVal + self.args[1].numVal)
            return self
        elif self.op == ProofOp.MINUS:
            if self.args[0].op == ProofOp.NUMVAL or self.args[1].op == ProofOp.NUMVAL:
                return ProofExpr.newNumVal(self.args[0].numVal - self.args[1].numVal)
            return self
        else:
            return self

    def __eq__(self, other: 'ProofExpr') -> bool:
        return self.numVal == other.numVal and self.op == other.op and self.args == other.args

    @staticmethod
    def newNumVal(val: int):
        return ProofExpr(val, ProofOp.NUMVAL, [])

    @staticmethod
    def newPlus(left: 'ProofExpr', right: 'ProofExpr'):
        return ProofExpr(None, ProofOp.PLUS, [left, right])

    @staticmethod
    def newMinus(left: 'ProofExpr', right: 'ProofExpr'):
        return ProofExpr(None, ProofOp.MINUS, [left, right])
    
class Proof:
    def __init__(self, relation: Relation, expr: ProofExpr) -> None:
        self.relation = relation
        self.expr = expr

    def __eq__(self, other: 'Proof') -> bool:
        return self.relation == other.relation and self.expr == other.expr

class ObjProofs:
    def __init__(self, proofs: List[Proof], fieldProofs: Dict[str, 'ObjProofs']) -> None:
        self.proofs = proofs
        self.fieldProofs = fieldProofs

    def __eq__(self, other: 'ObjProofs') -> bool:
        return self.proofs == other.proofs and self.fieldProofs == other.fieldProofs
