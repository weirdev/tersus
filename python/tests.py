from parser import *
from stdlib import *


def test1():
    test1 = """
    y = 2
    x = y
    affirm x = y
    x = test()
    z(x)
    y = 5
    """

    test1Expected = [
        Expr.newOpExpr(Op.newSetOp(SetOp('y', Expr.newNumExpr(2)))),
        Expr.newOpExpr(Op.newSetOp(SetOp('x', Expr.newVarExpr('y')))),
        Expr.newAffirmExpr(Affirm(Expr.newOpExpr(Op.newSetOp(SetOp('x', Expr.newVarExpr('y')))))),
        Expr.newOpExpr(Op.newSetOp(SetOp('x', Expr.newOpExpr(Op.newCallOp(CallOp('test', [])))))),
        Expr.newOpExpr(Op.newCallOp(CallOp('z', [Expr.newVarExpr('x')]))),
        Expr.newOpExpr(Op.newSetOp(SetOp('y', Expr.newNumExpr(5))))
        ]

    results = parse(test1)

    assert len(results) == len(test1Expected)

    for i in range(len(results)):
        try:
            assert results[i] == test1Expected[i]
        except Exception as e:
            print(i)
            raise e

def test2():
    test2 = """
    x = 5
    y = x
    affirm x = y
    x = add(x, y)
    """

    block = parse(test2)

    parentScope = EvalScope(None)
    parentScope.functions.update(StdLib)
    result = evalBlock(block, parentScope)

    assert result == 10

    parentScope = ProofScope(None)
    parentScope.functions.update(StdLib)
    result = proveBlock(block, parentScope).proofs

    assert len(result) == 1
    assert result[0] == Proof(Relation.EQ, ProofExpr.newNumVal(10))

def test3():
    test3 = """
    x = newArray(5)
    y = x.size
    i = {}
    affirm affirmEqToLt(i)
    affirm affirmEqToLt(x.size)
    affirm affirmLtToLtPlusN(i, 2)
    setArrayElement(x, i, 4)
    z = getArrayElement(x, 2)
    a = getArrayElement(x, 3)
    """
    
    # Prove
    # Succeed
    block = parse(test3.format("3"))
    parentScope = ProofScope(None)
    parentScope.functions.update(StdLib)
    proveBlock(block, parentScope)

    # Fail
    block = parse(test3.format("6"))
    parentScope = ProofScope(None)
    parentScope.functions.update(StdLib)
    failed = False
    try:
        proveBlock(block, parentScope)
    except:
        failed = True
    assert failed

    # Eval
    block = parse(test3.format("3"))
    parentScope = EvalScope(None)
    parentScope.functions.update(StdLib)
    result = evalBlock(block, parentScope)

    assert parentScope.vars["y"] == 5
    assert parentScope.vars["z"] == 0
    assert parentScope.vars["a"] == 4

if __name__ == '__main__':
    test3()

    test1()
    test2()
