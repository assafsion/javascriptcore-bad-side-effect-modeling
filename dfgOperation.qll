import cpp
import semmle.code.cpp.controlflow.Guards
import helperFunctions
import clobberWorldCall

Function getSpeculativeJitCompile(){
    result.hasQualifiedName("JSC::DFG::SpeculativeJIT::compile")
    and
    result.hasDefinition()
    and 
    exists
    (
        SwitchCase sc |
        sc.getEnclosingFunction() = result
    )
}

string getOpCodeSimpleCase(FunctionCall callOperation){
    exists
    (
        SwitchStmt op_stmt, SwitchCase op_case, FunctionCall op |
        op.getTarget().hasName("op")
        and
        (
            (op_stmt.getExpr() = op)
            or
            (op_stmt.getExpr().toString() = "op")
        )
        and
        op_case.getSwitchStmt() = op_stmt
        and
        callOperation.getAPredecessor*() = op_case
        and
        result = op_case.getExpr().toString()

    )
}

string getOpCodeByCompileOperation(FunctionCall callOperation){
    exists
    (
        Function compileFunc, FunctionCall compileFuncCall, SwitchStmt op_stmt, SwitchCase op_case, FunctionCall op | 
        compileFunc.getName().matches("compile%")
        and
        callOperation.getEnclosingFunction() = compileFunc
        and
        compileFunc.getACallToThisFunction() = compileFuncCall
        and
        op.getTarget().hasName("op")
        and
        (
            (op_stmt.getExpr() = op)
            or
            (op_stmt.getExpr().toString() = "op")
        )
        and
        op_case.getSwitchStmt() = op_stmt
        and
        compileFuncCall.getAPredecessor*() = op_case
        and
        result = op_case.getExpr().toString()
    )
    or
    // Compile function is wrapped by another function
    exists
    (
        Function compileFunc, FunctionCall compileFuncCall_1, FunctionCall compileFuncCall_2, SwitchStmt op_stmt, SwitchCase op_case, FunctionCall op | 
        compileFunc.getName().matches("compile%")
        and
        callOperation.getEnclosingFunction() = compileFunc
        and
        compileFunc.getACallToThisFunction() = compileFuncCall_1
        and
        compileFuncCall_1.getEnclosingFunction().getACallToThisFunction() = compileFuncCall_2
        and
        op.getTarget().hasName("op")
        and
        (
            (op_stmt.getExpr() = op)
            or
            (op_stmt.getExpr().toString() = "op")
        )
        and
        op_case.getSwitchStmt() = op_stmt
        and
        compileFuncCall_2.getAPredecessor*() = op_case
        and
        result = op_case.getExpr().toString()
    )
    or
    exists
    (
        SwitchStmt op_stmt, SwitchCase op_case, FunctionCall op, FlowFromOpCaseToCallOperation config, Expr source, Expr sink |
        op.getTarget().hasName("op")
        and
        (
            (op_stmt.getExpr() = op)
            or
            (op_stmt.getExpr().toString() = "op")
        )
        and
        op_case.getSwitchStmt() = op_stmt
        and
        op_case = source.getAPredecessor*()
        and
        op_case.getBasicBlock() = source.getBasicBlock()
        and
        sink = callOperation.getArgument(1)
        and
        config.hasFlow(DataFlow::exprNode(source), DataFlow::exprNode(sink))
        and
        result = op_case.getExpr().toString()
    )
}


// class DfgCaseOperation extends SwitchCase{

    
//     DfgCaseOperation()
//     {
//         exists
//         (
//             FunctionCall clobber, SwitchStmt executeEffectsOp, Function executeEffects, FunctionCall op |
//             executeEffects.hasName("executeEffects")
//             and
//             op.getTarget().hasName("op")
//             and
//             executeEffectsOp.getEnclosingFunction() = executeEffects
//             and
//             executeEffectsOp.getExpr() = op
//             and 
//             this.getSwitchStmt() = executeEffectsOp
//         )
//     }
// }

class DfgOperation extends Function{
    
    SwitchCase dfgEffectCase;
    FunctionCall dfgCallOperation;
    Function dfgCompile;
    string opCode;
    boolean isClobberWorldCalled;


    string strictTypeConstraintsNode1;
    string strictTypeConstraintsNode2;
    string strictTypeConstraintsNode3;
    string looseTypeConstraintsNode1;
    string looseTypeConstraintsNode2;
    string looseTypeConstraintsNode3;

    
    // string operandType;

    DfgOperation()
    {
        // Link the dfgOperation to the dfgCallOperation/dfgSlowCallOperation
        (
            (
                dfgCallOperation.getTarget().hasName("callOperation")
                and
                dfgCallOperation.getArgument(0) = this.getAnAccess()
            )
            or
            (
                dfgCallOperation.getTarget().hasName("slowPathCall")
                and
                dfgCallOperation.getArgument(2) = this.getAnAccess()
            )
        )
        and
        dfgCompile = getSpeculativeJitCompile()
        // We have 2 known options (all happens under the function SpeculativeJIT::compile):
        // 1) We call directly to the callOperation from the switch case
        // 2) We call to a wrapper function named compileSomeOperation from the switch case
        and
            (
                opCode = getOpCodeSimpleCase(dfgCallOperation)
                or
                opCode = getOpCodeByCompileOperation(dfgCallOperation)
            )
        and
        getConstraints(dfgCallOperation, 
            strictTypeConstraintsNode1, strictTypeConstraintsNode2, strictTypeConstraintsNode3, 
            looseTypeConstraintsNode1, looseTypeConstraintsNode2, looseTypeConstraintsNode3)
        

        // Find if ClobberWorld is called
        and 
        if exists
        (
            ClobberWorldCall clobber |
            clobber.getAnOpCode() = opCode
        )
        then isClobberWorldCalled = true
        else isClobberWorldCalled = false

        // What is left to do:
        // 1. Toggle if we call to toPrimitive
        
    }

    boolean hasACallToClobberWorld(){
        result = isClobberWorldCalled
    }

    Function getdfgCompile(){
        result = dfgCompile
    }

    FunctionCall getdfgCallOperation(){
        result = dfgCallOperation
    }

    string getOpcode(){
        result = opCode
    }

    string getNode1StrictConstraints(){
        result = strictTypeConstraintsNode1
    }

    string getNode2StrictConstraints(){
        result = strictTypeConstraintsNode2
    }

    string getNode3StrictConstraints(){
        result = strictTypeConstraintsNode3
    }

    string getNode1LooseConstraints(){
        result = looseTypeConstraintsNode1
    }

    string getNode2LooseConstraints(){
        result = looseTypeConstraintsNode2
    }

    string getNode3LooseConstraints(){
        result = looseTypeConstraintsNode3
    }
}

