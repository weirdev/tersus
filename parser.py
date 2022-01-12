from typing import Any, Dict, List, Optional
from enum import Enum
import re

from proof import *

affirmPattern = re.compile(r'affirm (.*)')
setOpPattern = re.compile(r'(\w+)\s*=(.*)')
callOpPattern = re.compile(r'(\w+)\((.*)\)')
varPattern = re.compile(r'\w+')
fieldAccessPattern = re.compile(r'(.+)\.(\w+)')
numPattern = re.compile(r'[0-9]+')

class Obj:
    def __init__(self, cls: str, val: Any, fields: Dict[str, Any]) -> None:
        self.cls = cls
        self.val = val
        self.fields = fields

    def getField(self, field: str) -> Any:
        return self.fields[field]

    def getVal(self) -> Any:
        return self.val

class EvalScope:
    def __init__(self, parent: Optional['EvalScope']) -> None:
        self.parent = parent
        self.vars: Dict[str, object] = {}
        self.functions: Dict[str, 'Expr'] = {}

    def getFn(self, functionName: str) -> Optional['Expr']:
        try:
            return self.functions[functionName]
        except KeyError:
            if self.parent is not None:
                return self.parent.getFn(functionName)
            else:
                return None

class ProofScope:
    def __init__(self, parent: Optional['ProofScope']) -> None:
        self.parent = parent
        self.proofs: Dict[str, ObjProofs] = {}
        self.functions: Dict[str, 'Expr'] = {}

    def getFn(self, functionName: str) -> Optional['Expr']:
        try:
            return self.functions[functionName]
        except KeyError:
            if self.parent is not None:
                return self.parent.getFn(functionName)
            else:
                return None

class ExprType(Enum):
    OP = 1 # Operation: <Op>
    AFF = 2 # Affirm: affirm <affirm>
    VAR = 3 # Variable: x
    NUM = 4 # Num: x

class OpType(Enum):
    SET = 1 # x = <expr>
    CALL = 2 # x(<expr>, <expr>, ...)
    FACC = 5 # FieldAccess: <expr>.y

class SetOp:
    def __init__(self, leftvar: str, expr: 'Expr') -> None:
        self.leftvar: str = leftvar
        self.expr: 'Expr' = expr

    def __eq__(self, other: 'SetOp'):
        return self.leftvar == other.leftvar and self.expr == other.expr

    def eval(self, scope: EvalScope):
        val = self.expr.eval(scope)
        scope.vars[self.leftvar] = val
        return val

    def prove(self, scope: ProofScope) -> ObjProofs:
        valProofs = self.expr.prove(scope)
        scope.proofs[self.leftvar] = valProofs
        return valProofs

class CallOp:
    def __init__(self, funcName: str, args: List['Expr']) -> None:
        self.funcName: str = funcName
        self.args: List['Expr'] = args
    
    def __eq__(self, other: 'CallOp') -> bool:
        return self.funcName == other.funcName and self.args == other.args

    def eval(self, scope: EvalScope):
        fn = scope.getFn(self.funcName)
        if fn is None:
            raise Exception("Unknown function")
        argResults = list(map(lambda x: x.eval(scope), self.args))
        fnScope = EvalScope(scope)
        return fn.eval(fnScope, *argResults)

    def prove(self, scope: ProofScope) -> ObjProofs:
        fn = scope.getFn(self.funcName)
        if fn is None:
            raise Exception("Unknown function")
        proofResults = list(map(lambda x: x.prove(scope), self.args))
        fnScope = ProofScope(scope)
        return fn.prove(fnScope, *proofResults)

class FieldAccessOp:
    def __init__(self, expr: 'Expr', field: str) -> None:
        self.expr = expr
        self.field = field
    
    def __eq__(self, other: 'FieldAccessOp') -> bool:
        return self.expr == other.expr and self.field == other.field

    def eval(self, scope: EvalScope):
        obj: Obj = self.expr.eval(scope)
        return obj.fields[self.field]

    def prove(self, scope: ProofScope) -> ObjProofs:
        proofs = self.expr.prove(scope)
        return proofs.fieldProofs[self.field]

class Op:
    def __init__(self, type: OpType, setOp: Optional[SetOp], callOp: Optional[CallOp], faOp: Optional[FieldAccessOp]) -> None:
        self.type: OpType = type
        self.setOp: Optional[SetOp] = setOp
        self.callOp: Optional[CallOp] = callOp
        self.faOp = faOp

    def __eq__(self, other: 'Op') -> bool:
        return self.type == other.type and self.setOp == other.setOp and self.callOp == other.callOp and self.faOp == other.faOp

    def eval(self, scope: EvalScope):
        if self.type == OpType.SET:
            return self.setOp.eval(scope)
        elif self.type == OpType.FACC:
            return self.faOp.eval(scope)
        else:
            return self.callOp.eval(scope)

    def proof(self, scope: ProofScope) -> ObjProofs:
        if self.type == OpType.SET:
            return self.setOp.prove(scope)
        elif self.type == OpType.FACC:
            return self.faOp.prove(scope)
        else:
            return self.callOp.prove(scope)

    @staticmethod
    def newSetOp(setOp: SetOp) -> 'Op':
        return Op(OpType.SET, setOp, None, None)

    @staticmethod
    def newCallOp(callOp: CallOp) -> 'Op':
        return Op(OpType.CALL, None, callOp, None)

    @staticmethod
    def newFieldAccessOp(faOp: FieldAccessOp) -> 'Op':
        return Op(OpType.FACC, None, None, faOp)

class Affirm: # affirm
    def __init__(self, proof) -> None:
        self.proof = proof

    def __eq__(self, other: 'Affirm') -> bool:
        return self.proof == other.proof

    def prove(self, scope: ProofScope) -> ObjProofs:
        return None

class Expr: # expr
    def __init__(self, type: ExprType, op: Optional[Op], affirm: Optional[Affirm], var: Optional[str], num: Optional[int]) -> None:
        self.type: ExprType = type
        self.op = op
        self.affirm = affirm
        self.var = var
        self.num = num

    def __eq__(self, other: 'Expr') -> bool:
        return (self.type == other.type and self.op == other.op and 
                self.affirm == other.affirm and self.var == other.var and 
                self.num == other.num)

    def eval(self, scope: EvalScope):
        if self.type == ExprType.OP:
            return self.op.eval(scope)
        elif self.type == ExprType.AFF:
            return None
        elif self.type == ExprType.VAR:
            return scope.vars[self.var]
        elif self.type == ExprType.NUM:
            return self.num

    def prove(self, scope: ProofScope) -> ObjProofs:
        if self.type == ExprType.OP:
            return self.op.proof(scope)
        elif self.type == ExprType.AFF:
            return self.affirm.prove(scope)
        elif self.type == ExprType.VAR:
            return scope.proofs[self.var]
        elif self.type == ExprType.NUM:
            return ObjProofs([Proof(Relation.EQ, ProofExpr.newNumVal(self.num))], {})

    @staticmethod
    def newOpExpr(op: Op) -> 'Expr':
        return Expr(ExprType.OP, op, None, None, None)

    @staticmethod
    def newAffirmExpr(affirm: Affirm) -> 'Expr':
        return Expr(ExprType.AFF, None, affirm, None, None)

    @staticmethod
    def newVarExpr(var: str) -> 'Expr':
        return Expr(ExprType.VAR, None, None, var, None)
        
    @staticmethod
    def newNumExpr(num: int) -> 'Expr':
        return Expr(ExprType.NUM, None, None, None, num)

    @staticmethod
    def parse(expr: str) -> 'Expr':
        expr = expr.strip()

        am = affirmPattern.fullmatch(expr)
        if am is not None:
            proof = am.group(1)
            return Expr.newAffirmExpr(Affirm(proof))
        
        sm = setOpPattern.fullmatch(expr)
        if sm is not None:
            leftVar = sm.group(1)
            rightExpr = Expr.parse(sm.group(2))
            return Expr.newOpExpr(Op.newSetOp(SetOp(leftVar, rightExpr)))

        cm = callOpPattern.fullmatch(expr)
        if cm is not None:
            functName = cm.group(1)
            argStrs = cm.group(2).strip()
            if (len(argStrs) == 0):
                args = []
            else:
                args = list(map(Expr.parse, argStrs.split(','))) # TODO: Need a CFG to do this correctly
            return Expr.newOpExpr(Op.newCallOp(CallOp(functName, args)))

        
        fap = fieldAccessPattern.fullmatch(expr)
        if fap is not None:
            leftExpr = Expr.parse(fap.group(1))
            rightFieldName = fap.group(2)
            return Expr.newOpExpr(Op.newFieldAccessOp(FieldAccessOp(leftExpr, rightFieldName)))

        nm = numPattern.fullmatch(expr)
        if nm is not None:
            return Expr.newNumExpr(int(expr))

        vm = varPattern.fullmatch(expr)
        if vm is not None:
            return Expr.newVarExpr(expr)


def parse(lines: str) -> List[Expr]:
    return list(map(
        Expr.parse, 
        filter(
            lambda l: len(l.strip()) > 0, 
            lines.splitlines())))

def evalBlock(block: List[Expr], scope: Optional[EvalScope] = None):
    last = None
    for expr in block:
        last = expr.eval(scope)
    return last

def proveBlock(block: List[Expr], scope: Optional[ProofScope] = None) -> ObjProofs:
    last = None
    for expr in block:
        last = expr.prove(scope)
    return last
