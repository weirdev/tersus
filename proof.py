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
    ANY = 4
    NESTED = 5

class ProofExpr:
    def __init__(self, numVal: Optional[int], op: ProofOp, args: List['ProofExpr'], nested: Optional['Proof']) -> None:
        self.numVal = numVal
        self.op = op
        self.args = args
        self.nested = nested

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

    def match(self, other: 'ProofExpr') -> bool:
        if self.op == ProofOp.ANY or other.op == ProofOp.ANY:
            return True

        if self.op == other.op:
            if self.op == ProofOp.PLUS or self.op == ProofOp.MINUS:
                return self.args[0].match(other.args[0]) and self.args[1].match(other.args[1])
            elif self.op == ProofOp.NUMVAL:
                if self.numVal is None or other.numVal is None:
                    return True
                else:
                    return self == other

        return False

    @staticmethod
    def newNumVal(val: int):
        return ProofExpr(val, ProofOp.NUMVAL, [], None)

    @staticmethod
    def newPlus(left: 'ProofExpr', right: 'ProofExpr'):
        return ProofExpr(None, ProofOp.PLUS, [left, right], None)

    @staticmethod
    def newMinus(left: 'ProofExpr', right: 'ProofExpr'):
        return ProofExpr(None, ProofOp.MINUS, [left, right], None)

    @staticmethod
    def newAny():
        return ProofExpr(None, ProofOp.ANY, [], None)
        
    @staticmethod
    def newNestedProof(proof: 'Proof'):
        return ProofExpr(None, ProofOp.NESTED, [], proof)
    
class Proof:
    def __init__(self, relation: Relation, expr: ProofExpr) -> None:
        self.relation = relation
        self.expr = expr

    def __eq__(self, other: 'Proof') -> bool:
        return self.relation == other.relation and self.expr == other.expr

    def match(self, other: 'Proof') -> bool:
        return self.relation == other.relation and self.expr.match(other.expr)

class ObjProofs:
    def __init__(self, proofs: List[Proof], fieldProofs: Dict[str, 'ObjProofs']) -> None:
        self.proofs = proofs
        self.fieldProofs = fieldProofs

    def __eq__(self, other: 'ObjProofs') -> bool:
        return self.proofs == other.proofs and self.fieldProofs == other.fieldProofs
