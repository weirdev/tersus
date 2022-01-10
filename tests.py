from parser import *


def test1():
    test1 = """
    x = y
    affirm x = y
    x = test()
    z(x)
    y = 5
    """

    test1Expected = [
        Expr.newOpExpr(Op.newSetOp(SetOp('x', Expr.newVarExpr('y')))),
        Expr.newAffirmExpr(Affirm('x = y')),
        Expr.newOpExpr(Op.newSetOp(SetOp('x', Expr.newOpExpr(Op.newCallOp(CallOp('test', [])))))),
        Expr.newOpExpr(Op.newCallOp(CallOp('z', [Expr.newVarExpr('x')]))),
        Expr.newOpExpr(Op.newSetOp(SetOp('y', Expr.newNumExpr(5))))
        ]

    results = parse(test1)

    assert len(results) == len(test1Expected)

    for i in range(len(results)):
        try:
            assert results[i] == test1Expected[i]
        except:
            print(i)

class TestFuncInst:
    def __init__(self, f, p) -> None:
        self.f = f
        self.p = p

    def eval(self, scope: EvalScope, *args):
        return self.f((scope,) + args)

    def prove(self, scope: ProofScope, *args):
        return self.p((scope,) + args)

def addProve(args):
    lhs = args[1]
    rhs = args[2]

    if isinstance(lhs[0], int):
        if isinstance(rhs[0], int):
            return [lhs[0] + rhs[0]]

def test2():
    test2 = """
    x = 5
    y = x
    affirm x = y
    x = add(x, y)
    """

    block = parse(test2)

    parentScope = EvalScope(None)
    addFunct = TestFuncInst(lambda x: x[1] + x[2], addProve)
    parentScope.functions['add'] = addFunct
    result = evalBlock(block, parentScope)

    assert result == 10
    print(result)

    parentScope = ProofScope(None)
    parentScope.functions['add'] = addFunct
    result = proveBlock(block, parentScope)

    assert result[0] == 10

if __name__ == '__main__':
    test2()