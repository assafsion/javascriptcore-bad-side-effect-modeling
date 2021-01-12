import cpp
import helperFunctionType
import semmle.code.cpp.dataflow.DataFlow
import semmle.code.cpp.dataflow.TaintTracking


// Some classes and predicates I wrote to simplify the readability of the query

// DfgCallOperation helper functions

// This class analyze the function  DFGSpeculativeJIT64.cpp/compile and lik between the operation code to the actual operation
class FlowFromOpCaseToCallOperation extends DataFlow::Configuration {
    FlowFromOpCaseToCallOperation() { this = "FlowFromOpCaseToCallOperation" }
  
    override predicate isSource(DataFlow::Node source) {
      exists (SwitchCase op |
        source.asExpr().getBasicBlock() = op.getBasicBlock()
      )
    }
  
    override predicate isSink(DataFlow::Node sink) {
      exists (FunctionCall fc |
        sink.asExpr() = fc.getArgument(1) and
        fc.getTarget().getName().matches("%callOperation%")
      )
    }
  }


class LinkOperationToExecVM extends TaintTracking::Configuration {
    LinkOperationToExecVM() { this = "LinkOperationToExecVM" }

    override predicate isSource(DataFlow::Node source) {
        exists
        (
            Function operation | 
            source.asParameter() = operation.getAParameter()
        )
    }

    override predicate isSink(DataFlow::Node sink) {
        exists
        (
            Expr exp | 
            sink.asExpr() = exp 
        )
    }
}

// This class finds variables that were converted to JSObjects:
// someFunc(JSValue arg0){
//     ...
//     arg0_copy = asObject(arg0)   
//}
// We will find arg0_copy
class ConvertToObjectAndCall extends DataFlow::Configuration {
    ConvertToObjectAndCall() { this = "ConvertToObjectAndCall" }

    override predicate isSource(DataFlow::Node source) {
        exists
        (
            FunctionCall operation |
            operation.getTarget().hasName("asObject") 
            and
            source.asExpr() = operation
        )
    }

    override predicate isSink(DataFlow::Node sink) {
        exists
        (
            VariableAccess jsObj, FunctionCall fc |
            fc.getQualifier() = jsObj
            and
            jsObj.getType().hasName("JSObject *")
            and
            sink.asExpr() = jsObj
        )
    }
}

// Find what argument type we need to have based on guards
string getStrictTypeFromGuard(FunctionCall callOperation, string childNum){
    exists
    (
        GuardCondition gc, BasicBlock bb, FunctionCall useKind, Expr left, Expr right |
        useKind.getTarget().hasName("useKind")
        and
        bb = callOperation.getBasicBlock()
        and
        gc.ensuresEq(left, right, 0, bb, true)
        and
        (
            (left = useKind and useKind.getQualifier().(FunctionCall).getTarget().hasName(childNum) and result = right.toString())
            or
            (right = useKind and useKind.getQualifier().(FunctionCall).getTarget().hasName(childNum) and result = left.toString())
        )    
    )
}

// Find what argument type we must not have based on guards
string getLooseTypeFromGuard(FunctionCall callOperation, string childNum){
    exists
    (
        GuardCondition gc, BasicBlock bb, FunctionCall useKind, Expr left, Expr right |
        useKind.getTarget().hasName("useKind")
        and
        bb = callOperation.getBasicBlock()
        and
        gc.ensuresEq(left, right, 0, bb, false)
        and
        (
            (left = useKind and useKind.getQualifier().(FunctionCall).getTarget().hasName(childNum) and result = right.toString())
            or
            (right = useKind and useKind.getQualifier().(FunctionCall).getTarget().hasName(childNum) and result = left.toString())
        )    
    )
}

// Find what argument type we need to have based on switch cases
string getStrictTypeFromSwitchCase(FunctionCall callOperation, string childNum){
    exists
    (
        SwitchStmt st, SwitchCase case, FunctionCall useKind |
        
        useKind.getTarget().hasName("useKind")
        and
        st.getExpr() = useKind
        and
        useKind.getQualifier().(FunctionCall).getTarget().hasName(childNum)
        and
        case.getSwitchStmt() = st
        and
        callOperation.getAPredecessor*() = case
        and
        result = case.getExpr().toString()
    )
}


// Find what the 1st argument type can't be based on switch cases and guards
string getLooseTypeConstraintsForChild1(FunctionCall callOperation){
    result = getLooseTypeFromGuard(callOperation, "child1")
    or
    (
        result = "NoLooseConstraint"
        and
        not exists
        (
            GuardCondition gc, BasicBlock bb, FunctionCall useKind, Expr left, Expr right | 
            useKind.getTarget().hasName("useKind")
            and
            bb = callOperation.getBasicBlock()
            and
            gc.ensuresEq(left, right, 0, bb, false)
            and
            (
                (left = useKind and useKind.getQualifier().(FunctionCall).getTarget().hasName("child1"))
                or
                (right = useKind and useKind.getQualifier().(FunctionCall).getTarget().hasName("child1"))
            ) 
        )
    )

}

// Find what the 2nd argument type can't be based on switch cases and guards
string getLooseTypeConstraintsForChild2(FunctionCall callOperation){
    result = getLooseTypeFromGuard(callOperation, "child2")
    or
    (
        result = "NoLooseConstraint"
        and
        not exists
        (
            GuardCondition gc, BasicBlock bb, FunctionCall useKind, Expr left, Expr right | 
            useKind.getTarget().hasName("useKind")
            and
            bb = callOperation.getBasicBlock()
            and
            gc.ensuresEq(left, right, 0, bb, false)
            and
            (
                (left = useKind and useKind.getQualifier().(FunctionCall).getTarget().hasName("child2"))
                or
                (right = useKind and useKind.getQualifier().(FunctionCall).getTarget().hasName("child2"))
            ) 
        )
    )

}

// Find what the 3rd argument type can't be based on switch cases and guards
string getLooseTypeConstraintsForChild3(FunctionCall callOperation){
    result = getLooseTypeFromGuard(callOperation, "child3")
    or
    (
        result = "NoLooseConstraint"
        and
        not exists
        (
            GuardCondition gc, BasicBlock bb, FunctionCall useKind, Expr left, Expr right | 
            useKind.getTarget().hasName("useKind")
            and
            bb = callOperation.getBasicBlock()
            and
            gc.ensuresEq(left, right, 0, bb, false)
            and
            (
                (left = useKind and useKind.getQualifier().(FunctionCall).getTarget().hasName("child3"))
                or
                (right = useKind and useKind.getQualifier().(FunctionCall).getTarget().hasName("child3"))
            ) 
        )
    )

}

// Find what the 1st argument type must be based on switch cases and guards
string getStrictTypeConstraintsForChild1(FunctionCall callOperation){
    result = getStrictTypeFromGuard(callOperation, "child1")
    or
    result = getStrictTypeFromSwitchCase(callOperation, "child1")
    or
    (
        result = "NoStrictConstraint"
        and
        not exists
        (
            SwitchCase case, SwitchStmt st, FunctionCall useKind |
            case.getSwitchStmt() = st
            and
            useKind.getTarget().hasName("useKind")
            and
            st.getExpr() = useKind
            and
            useKind.getQualifier().(FunctionCall).getTarget().hasName("child1")
            and
            callOperation.getAPredecessor+() = case
        )
        and 
        not exists
        (
            GuardCondition gc, BasicBlock bb, FunctionCall useKind, Expr left, Expr right | 
            useKind.getTarget().hasName("useKind")
            and
            bb = callOperation.getBasicBlock()
            and
            gc.ensuresEq(left, right, 0, bb, true)
            and
            (
                (left = useKind and useKind.getQualifier().(FunctionCall).getTarget().hasName("child1"))
                or
                (right = useKind and useKind.getQualifier().(FunctionCall).getTarget().hasName("child1"))
            ) 
        )
    )
}

// Find what the 2nd argument type must be based on switch cases and guards
string getStrictTypeConstraintsForChild2(FunctionCall callOperation){
    result = getStrictTypeFromGuard(callOperation, "child2")
    or
    result = getStrictTypeFromSwitchCase(callOperation, "child2")
    or
    (
        result = "NoStrictConstraint"
        and
        not exists
        (
            SwitchCase case, SwitchStmt st, FunctionCall useKind |
            case.getSwitchStmt() = st
            and
            useKind.getTarget().hasName("useKind")
            and
            st.getExpr() = useKind
            and
            useKind.getQualifier().(FunctionCall).getTarget().hasName("child2")
            and
            callOperation.getAPredecessor+() = case
        )
        and 
        not exists
        (
            GuardCondition gc, BasicBlock bb, FunctionCall useKind, Expr left, Expr right | 
            useKind.getTarget().hasName("useKind")
            and
            bb = callOperation.getBasicBlock()
            and
            gc.ensuresEq(left, right, 0, bb, true)
            and
            (
                (left = useKind and useKind.getQualifier().(FunctionCall).getTarget().hasName("child2"))
                or
                (right = useKind and useKind.getQualifier().(FunctionCall).getTarget().hasName("child2"))
            ) 
        )
    )
}

// Find what the 3rd argument type must be based on switch cases and guards
string getStrictTypeConstraintsForChild3(FunctionCall callOperation){
    result = getStrictTypeFromGuard(callOperation, "child3")
    or
    result = getStrictTypeFromSwitchCase(callOperation, "child3")
    or
    (
        result = "NoStrictConstraint"
        and
        not exists
        (
            SwitchCase case, SwitchStmt st, FunctionCall useKind |
            case.getSwitchStmt() = st
            and
            useKind.getTarget().hasName("useKind")
            and
            st.getExpr() = useKind
            and
            useKind.getQualifier().(FunctionCall).getTarget().hasName("child3")
            and
            callOperation.getAPredecessor+() = case
        )
        and 
        not exists
        (
            GuardCondition gc, BasicBlock bb, FunctionCall useKind, Expr left, Expr right | 
            useKind.getTarget().hasName("useKind")
            and
            bb = callOperation.getBasicBlock()
            and
            gc.ensuresEq(left, right, 0, bb, true)
            and
            (
                (left = useKind and useKind.getQualifier().(FunctionCall).getTarget().hasName("child3"))
                or
                (right = useKind and useKind.getQualifier().(FunctionCall).getTarget().hasName("child3"))
            ) 
        )
    )
}

// Find all type constraints
predicate getConstraints(
    FunctionCall callOperation, 
    string node1StrictConstraints, 
    string node2StrictConstraints, 
    string node3StrictConstraints, 
    string node1LooseConstraints, 
    string node2LooseConstraints, 
    string node3LooseConstraints){

        // node1StrictConstraints = getStrictTypeConstraintsForChild1(callOperation)
        // and
        // node2StrictConstraints = getStrictTypeConstraintsForChild2(callOperation)
        // and
        // node3StrictConstraints = getStrictTypeConstraintsForChild3(callOperation)
        // and
        // node1LooseConstraints = getLooseTypeConstraintsForChild1(callOperation)
        // and 
        // node2LooseConstraints = getLooseTypeConstraintsForChild2(callOperation)
        // and 
        // node3LooseConstraints = getLooseTypeConstraintsForChild3(callOperation)

    getStrictTypeConstraints(callOperation, node1StrictConstraints, node2StrictConstraints, node3StrictConstraints)
    and
    getLooseTypeConstraints(callOperation, node1LooseConstraints, node2LooseConstraints, node3LooseConstraints)
}


// ClobberWorldCall helper functions

// This predicate all empty blocks in a switch case:
// switch(lala){
//  case notEmpty:
//      printf("lel");
//      break;
//  case empty:
//  case notEmpty2:
//      printf("lol");
//      break;
//
//}
predicate isEmpty(SwitchCase case){
    case.getBasicBlock().length() = 1
}

predicate isClobberReachableFromCaseSimpleCase(FunctionCall clobberWorld, SwitchCase case){
    (
        case.getBasicBlock().contains(clobberWorld)
    )
    or
    (
        isEmpty(case) 
        and
        isClobberReachableFromCaseSimpleCase(clobberWorld, case.getNextSwitchCase())
    )
}

boolean isClobberInsideIfStatement(FunctionCall clobberWorld, string funcName){
    
    exists
    (
        GuardCondition gc, BasicBlock bb, FunctionCall fc, Expr left, Expr right | 
        bb = clobberWorld.getBasicBlock()
        and
        fc.getTarget().hasName(funcName)
        and 
        if  (
                gc.ensuresEq(left, right, 0, bb, true)
                and
                gc.getAChild*() = fc
            )
        then result = true
        else result = false
    ) 
}

boolean isClobberInsideSimpleSwitchCase(FunctionCall clobberWorld, string funcName)
{
    exists
    (
        SwitchCase case, SwitchStmt st, FunctionCall fc |
        fc.getTarget().hasName(funcName)
        and
        st.getExpr() = fc
        and
        case.getSwitchStmt() = st
        and
        if case.getBasicBlock().contains(clobberWorld)
        then result = true
        else result = false
    )
}

boolean isClobberInsideComplexedSwitchCase(FunctionCall clobberWorld, string funcName){
    exists
    (
        SwitchCase case, SwitchStmt st, FunctionCall fc |
        fc.getTarget().hasName(funcName)
        and
        st.getExpr() = fc
        and
        case.getSwitchStmt() = st
        and
        if clobberWorld.getAPredecessor*() = case
        then result = true
        else result = false
    )  
}

boolean isClobberInsideSwitchOrIfChild1(FunctionCall clobberWorld){ 
    if exists
        (
            FunctionCall fc, string funcName, SwitchCase case, SwitchStmt st |
            (
                funcName = "useKind"
                and
                fc.getTarget().hasName(funcName)
                and
                fc.getQualifier().(FunctionCall).getTarget().hasName("child1")
                and
                st.getExpr() = fc
                and
                case.getSwitchStmt() = st
                and
                clobberWorld.getAPredecessor*() = case
            )
            or
            (
                funcName = "binaryUseKind"
                and
                fc.getTarget().hasName(funcName)
                and
                st.getExpr() = fc
                and
                case.getSwitchStmt() = st
                and
                clobberWorld.getAPredecessor*() = case
            )
        )
    then result = true
    else if exists
            (
                GuardCondition gc, BasicBlock bb, FunctionCall fc, Expr left, Expr right, string funcName |

                (
                    funcName = "useKind"
                    and 
                    bb = clobberWorld.getBasicBlock()
                    and
                    fc.getTarget().hasName(funcName)
                    and
                    fc.getQualifier().(FunctionCall).getTarget().hasName("child1")
                    and 
                    gc.ensuresEq(left, right, 0, bb, true)
                    and
                    gc.getAChild*() = fc
                )  
                or
                (
                    funcName = "binaryUseKind"
                    and 
                    bb = clobberWorld.getBasicBlock()
                    and
                    fc.getTarget().hasName("child1")
                    and 
                    gc.ensuresEq(left, right, 0, bb, true)
                    and
                    gc.getAChild*() = fc
                )
                or
                (
                    funcName = "isBinaryUseKind"
                    and 
                    bb = clobberWorld.getBasicBlock()
                    and
                    fc.getTarget().hasName(funcName)
                    and 
                    gc.ensuresEq(left, right, 0, bb, true)
                    and
                    gc.getAChild*() = fc
                )
            )
        then result = true 
        else result = false 
}

boolean isClobberInsideSwitchOrIfChild2(FunctionCall clobberWorld){ 
    if exists
        (
            FunctionCall fc, string funcName, SwitchCase case, SwitchStmt st |
            (
                funcName = "useKind"
                and
                fc.getTarget().hasName(funcName)
                and
                fc.getQualifier().(FunctionCall).getTarget().hasName("child2")
                and
                st.getExpr() = fc
                and
                case.getSwitchStmt() = st
                and
                clobberWorld.getAPredecessor*() = case
            )
            or
            (
                funcName = "binaryUseKind"
                and
                fc.getTarget().hasName(funcName)
                and
                st.getExpr() = fc
                and
                case.getSwitchStmt() = st
                and
                clobberWorld.getAPredecessor*() = case
            )
        )
    then result = true
    else if exists
            (
                GuardCondition gc, BasicBlock bb, FunctionCall fc, Expr left, Expr right, string funcName |

                (
                    funcName = "useKind"
                    and 
                    bb = clobberWorld.getBasicBlock()
                    and
                    fc.getTarget().hasName(funcName)
                    and
                    fc.getQualifier().(FunctionCall).getTarget().hasName("child2")
                    and 
                    gc.ensuresEq(left, right, 0, bb, true)
                    and
                    gc.getAChild*() = fc
                )   
                or
                (
                    funcName = "binaryUseKind"
                    and 
                    bb = clobberWorld.getBasicBlock()
                    and
                    fc.getTarget().hasName("child2")
                    and 
                    gc.ensuresEq(left, right, 0, bb, true)
                    and
                    gc.getAChild*() = fc
                )
                or
                (
                    funcName = "isBinaryUseKind"
                    and 
                    bb = clobberWorld.getBasicBlock()
                    and
                    fc.getTarget().hasName(funcName)
                    and 
                    gc.ensuresEq(left, right, 0, bb, true)
                    and
                    gc.getAChild*() = fc
                )
            )
        then result = true 
        else result = false 
}

boolean isClobberInsideSwitchOrIfChild3(FunctionCall clobberWorld){ 
    if exists
        (
            FunctionCall fc, string funcName, SwitchCase case, SwitchStmt st |
            (
                funcName = "useKind"
                and
                fc.getTarget().hasName(funcName)
                and
                fc.getQualifier().(FunctionCall).getTarget().hasName("child3")
                and
                st.getExpr() = fc
                and
                case.getSwitchStmt() = st
                and
                clobberWorld.getAPredecessor*() = case
            )
        )
    then result = true
    else if exists
            (
                GuardCondition gc, BasicBlock bb, FunctionCall fc, Expr left, Expr right, string funcName |

                (
                    funcName = "useKind"
                    and 
                    bb = clobberWorld.getBasicBlock()
                    and
                    fc.getTarget().hasName(funcName)
                    and
                    fc.getQualifier().(FunctionCall).getTarget().hasName("child3")
                    and 
                    gc.ensuresEq(left, right, 0, bb, true)
                    and
                    gc.getAChild*() = fc
                )
            )
        then result = true 
        else result = false 
}

boolean doesClobberMightHaveLooseTypesChild1(FunctionCall clobberWorld){ 
    if exists
        (
            FunctionCall fc, string funcName, SwitchCase case1, SwitchCase case2, SwitchStmt st |
            (
                funcName = "useKind"
                and
                fc.getTarget().hasName(funcName)
                and
                fc.getQualifier().(FunctionCall).getTarget().hasName("child1")
                and
                st.getExpr() = fc
                and
                case1.getSwitchStmt() = st
                and
                case2.getSwitchStmt() = st
                and
                clobberWorld.getAPredecessor*() = case1
                and
                not clobberWorld.getAPredecessor*() = case2
            )
            or
            (
                funcName = "binaryUseKind"
                and
                fc.getTarget().hasName(funcName)
                and
                st.getExpr() = fc
                and
                case1.getSwitchStmt() = st
                and
                case2.getSwitchStmt() = st
                and
                clobberWorld.getAPredecessor*() = case1
                and
                not clobberWorld.getAPredecessor*() = case2
            )
        )
    then result = true
    else if exists
            (
                GuardCondition gc, BasicBlock bb, FunctionCall fc, Expr left, Expr right, string funcName |

                (
                    funcName = "useKind"
                    and 
                    bb = clobberWorld.getBasicBlock()
                    and
                    fc.getTarget().hasName(funcName)
                    and
                    fc.getQualifier().(FunctionCall).getTarget().hasName("child1")
                    and 
                    gc.controls(bb, false)
                    and
                    gc.getAChild*() = fc
                )  
                or
                (
                    funcName = "binaryUseKind"
                    and 
                    bb = clobberWorld.getBasicBlock()
                    and
                    fc.getTarget().hasName("child1")
                    and 
                    gc.controls(bb, false)
                    and
                    gc.getAChild*() = fc
                )
                or
                (
                    funcName = "isBinaryUseKind"
                    and 
                    bb = clobberWorld.getBasicBlock()
                    and
                    fc.getTarget().hasName(funcName)
                    and 
                    gc.controls(bb, false)
                    and
                    gc.getAChild*() = fc
                )
            )
        then result = true 
        else result = false 
}

boolean doesClobberMightHaveLooseTypesChild2(FunctionCall clobberWorld){ 
    if exists
        (
            FunctionCall fc, string funcName, SwitchCase case1, SwitchCase case2, SwitchStmt st |
            (
                funcName = "useKind"
                and
                fc.getTarget().hasName(funcName)
                and
                fc.getQualifier().(FunctionCall).getTarget().hasName("child2")
                and
                st.getExpr() = fc
                and
                case1.getSwitchStmt() = st
                and
                case2.getSwitchStmt() = st
                and
                clobberWorld.getAPredecessor*() = case1
                and
                not clobberWorld.getAPredecessor*() = case2
            )
            or
            (
                funcName = "binaryUseKind"
                and
                fc.getTarget().hasName(funcName)
                and
                st.getExpr() = fc
                and
                case1.getSwitchStmt() = st
                and
                case2.getSwitchStmt() = st
                and
                clobberWorld.getAPredecessor*() = case1
                and
                not clobberWorld.getAPredecessor*() = case2
            )
        )
    then result = true
    else if exists
            (
                GuardCondition gc, BasicBlock bb, FunctionCall fc, Expr left, Expr right, string funcName |

                (
                    funcName = "useKind"
                    and 
                    bb = clobberWorld.getBasicBlock()
                    and
                    fc.getTarget().hasName(funcName)
                    and
                    fc.getQualifier().(FunctionCall).getTarget().hasName("child2")
                    and 
                    gc.controls(bb, false)
                    and
                    gc.getAChild*() = fc
                )  
                or
                (
                    funcName = "binaryUseKind"
                    and 
                    bb = clobberWorld.getBasicBlock()
                    and
                    fc.getTarget().hasName("child2")
                    and 
                    gc.controls(bb, false)
                    and
                    gc.getAChild*() = fc
                )
                or
                (
                    funcName = "isBinaryUseKind"
                    and 
                    bb = clobberWorld.getBasicBlock()
                    and
                    fc.getTarget().hasName(funcName)
                    and 
                    gc.controls(bb, false)
                    and
                    gc.getAChild*() = fc
                )
            )
        then result = true 
        else result = false 
}

boolean doesClobberMightHaveLooseTypesChild3(FunctionCall clobberWorld){ 
    if exists
        (
            FunctionCall fc, string funcName, SwitchCase case1, SwitchCase case2, SwitchStmt st |
            (
                funcName = "useKind"
                and
                fc.getTarget().hasName(funcName)
                and
                fc.getQualifier().(FunctionCall).getTarget().hasName("child3")
                and
                st.getExpr() = fc
                and
                case1.getSwitchStmt() = st
                and
                case2.getSwitchStmt() = st
                and
                clobberWorld.getAPredecessor*() = case1
                and
                not clobberWorld.getAPredecessor*() = case2
            )
        )
    then result = true
    else if exists
            (
                GuardCondition gc, BasicBlock bb, FunctionCall fc, Expr left, Expr right, string funcName |

                (
                    funcName = "useKind"
                    and 
                    bb = clobberWorld.getBasicBlock()
                    and
                    fc.getTarget().hasName(funcName)
                    and
                    fc.getQualifier().(FunctionCall).getTarget().hasName("child3")
                    and 
                    gc.controls(bb, false)
                    and
                    gc.getAChild*() = fc
                )  
            )
        then result = true 
        else result = false 
}

string getFromComplexedCaseOpCode(FunctionCall clobberWorld){
    // "Complexed" == Basic Block bigger than 1, saves some execution time to split between simple and complexed
    // We first need to find the most inner case statement
    exists
    (
        SwitchStmt st, SwitchCase case |
        st = getInnerSwitchStatement(clobberWorld, "op")
        and
        case.getSwitchStmt() = st
        and
        case.getASuccessor+() = clobberWorld
        and
        result = case.getExpr().toString()
    )
}

string getFromSimpleCaseOpCode(FunctionCall clobberWorld){
    exists
    (
        SwitchCase case | 
        isClobberReachableFromCaseSimpleCase(clobberWorld, case)
        and
        result = case.getExpr().toString()
    )

}

string getOpForClobberFromIfStatement(FunctionCall clobberWorld){
    exists
    (
        GuardCondition gc, BasicBlock bb, FunctionCall op, Expr left, Expr right | 
        bb = clobberWorld.getBasicBlock()
        and
        op.getTarget().hasName("op")
        and 
        gc.ensuresEq(left, right, 0, bb, true)
        and
        (
            left = op and result = right.toString()
            or 
            right = op and result = left.toString()
        )
    )
}

SwitchStmt getInnerSwitchStatement(FunctionCall clobberWorld, string funcName){
    
    exists
    (
        FunctionCall fc | 
        result.getExpr() = fc
        and
        fc.getTarget().hasName(funcName)
    )
    and
    result.getASuccessor+() = clobberWorld
    and
    not exists
    (
        SwitchStmt innerStatement, FunctionCall fc | 
        innerStatement.getExpr() = fc
        and
        fc.getTarget().hasName(funcName)
        and
        result.getASuccessor+() = innerStatement
        and
        innerStatement.getASuccessor+() = clobberWorld
        
    )
}

string getOpForClobberWorld(FunctionCall clobberWorld){
    // 1. Inside an if
     
    if isClobberInsideIfStatement(clobberWorld, "op") = true
    then result = getOpForClobberFromIfStatement(clobberWorld)
    else 
        if isClobberInsideSimpleSwitchCase(clobberWorld, "op") = true
        then result = getFromSimpleCaseOpCode(clobberWorld)
        else if isClobberInsideComplexedSwitchCase(clobberWorld, "op") = true
             then result = getFromComplexedCaseOpCode(clobberWorld)
             else result = "NoOpCodeFound"

    
    // 2. Inside a simple switch case
    // 3. Inside an else statement - (if must be node->op())

}

string getStrictTypeForClobberWorldChild1(FunctionCall clobberWorld){
    if 
    (
        isClobberInsideSwitchOrIfChild1(clobberWorld) = true
    )
    then
    (
        exists
        (
            SwitchCase case, SwitchStmt st, FunctionCall call |
            st = getInnerSwitchStatement(clobberWorld, "useKind")
            and
            st.getExpr() = call
            and
            call.getQualifier().(FunctionCall).getTarget().hasName("child1")
            and
            case.getSwitchStmt() = st
            and
            case.getASuccessor*() = clobberWorld
            and
            result = case.getExpr().toString()
        )
        or 
        exists
        (
            SwitchCase case, SwitchStmt st, FunctionCall call |
            st = getInnerSwitchStatement(clobberWorld, "binaryUseKind")
            and
            st.getExpr() = call
            and
            case.getSwitchStmt() = st
            and
            case.getASuccessor*() = clobberWorld
            and
            result = case.getExpr().toString()
        )
        or
        exists
        (
            GuardCondition gc, Expr left, Expr right |
            // gc.controls(clobberWorld.getBasicBlock(), true)
            gc.ensuresEq(left, right, 0, clobberWorld.getBasicBlock(), true)
            and
            (
                exists
                (
                    UseKindExpr useKind | 
                    gc.getAChild*() = useKind
                    and
                    "child1" = useKind.getChildNum()
                    and
                    result = useKind.getComparedToType()
                )
                or
                exists
                (
                    BinaryUseKindExpr binaryUseKind | 
                    gc.getAChild*() = binaryUseKind
                    and
                    "child1" = binaryUseKind.getChildNum()
                    and
                    result = binaryUseKind.getComparedToType()
                )
                or
                exists
                (
                    IsBinaryUseKind isBinaryUseKind | 
                    gc.getAChild*() = isBinaryUseKind
                    and
                    "child1" = isBinaryUseKind.getChildNum()
                    and
                    result = isBinaryUseKind.getComparedToType()
                )
            )
        )
    )
    else 
        result = "noTypeConstraintsFound"
}

string getStrictTypeForClobberWorldChild2(FunctionCall clobberWorld){
    if 
    (
        isClobberInsideSwitchOrIfChild2(clobberWorld) = true
    )
    then
    (
        exists
        (
            SwitchCase case, SwitchStmt st, FunctionCall call |
            st = getInnerSwitchStatement(clobberWorld, "useKind")
            and
            st.getExpr() = call
            and
            call.getQualifier().(FunctionCall).getTarget().hasName("child2")
            and
            case.getSwitchStmt() = st
            and
            case.getASuccessor*() = clobberWorld
            and
            result = case.getExpr().toString()
        )
        or 
        exists
        (
            SwitchCase case, SwitchStmt st, FunctionCall call |
            st = getInnerSwitchStatement(clobberWorld, "binaryUseKind")
            and
            st.getExpr() = call
            and
            case.getSwitchStmt() = st
            and
            case.getASuccessor*() = clobberWorld
            and
            result = case.getExpr().toString()
        )
        or
        exists
        (
            GuardCondition gc |
            gc.controls(clobberWorld.getBasicBlock(), true)
            and
            (
                exists
                (
                    UseKindExpr useKind | 
                    gc.getAChild*() = useKind
                    and
                    "child2" = useKind.getChildNum()
                    and
                    result = useKind.getComparedToType()
                )
                or
                exists
                (
                    BinaryUseKindExpr binaryUseKind | 
                    gc.getAChild*() = binaryUseKind
                    and
                    "child2" = binaryUseKind.getChildNum()
                    and
                    result = binaryUseKind.getComparedToType()
                )
                or
                exists
                (
                    IsBinaryUseKind isBinaryUseKind | 
                    gc.getAChild*() = isBinaryUseKind
                    and
                    "child2" = isBinaryUseKind.getChildNum()
                    and
                    result = isBinaryUseKind.getComparedToType()
                )
            )
        )
    )
    else 
        result = "noTypeConstraintsFound"
}

string getStrictTypeForClobberWorldChild3(FunctionCall clobberWorld){
    if 
    (
        isClobberInsideSwitchOrIfChild3(clobberWorld) = true
    )
    then
    (
        exists
        (
            SwitchCase case, SwitchStmt st, FunctionCall call |
            st = getInnerSwitchStatement(clobberWorld, "useKind")
            and
            st.getExpr() = call
            and
            call.getQualifier().(FunctionCall).getTarget().hasName("child3")
            and
            case.getSwitchStmt() = st
            and
            case.getASuccessor*() = clobberWorld
            and
            result = case.getExpr().toString()
        )
        or 
        exists
        (
            GuardCondition gc |
            gc.controls(clobberWorld.getBasicBlock(), true)
            and
            (
                exists
                (
                    UseKindExpr useKind | 
                    gc.getAChild*() = useKind
                    and
                    "child3" = useKind.getChildNum()
                    and
                    result = useKind.getComparedToType()
                )
            )
        )
    )
    else 
        result = "noTypeConstraintsFound"
}

string getLooseTypeForClobberWorldChild1(FunctionCall clobberWorld){
    // Extracting loose types from switch case
    if doesClobberMightHaveLooseTypesChild1(clobberWorld) = true
    then 
    (
        exists
        (
            SwitchStmt st, SwitchCase case | 
            st = getInnerSwitchStatement(clobberWorld, "useKind")
            and
            st.getExpr().(FunctionCall).getQualifier().(FunctionCall).getTarget().hasName("child1")
            and
            case.getSwitchStmt() = st
            and
            (
                not clobberWorld.getAPredecessor+() = case
            )
            and result = case.getExpr().toString()
        )
        or
        exists
        (
            SwitchStmt st, SwitchCase case | 
            st = getInnerSwitchStatement(clobberWorld, "binaryUseKind")
            and
            case.getSwitchStmt() = st
            and
            (
                not clobberWorld.getAPredecessor+() = case
            )
            and result = case.getExpr().toString()
        )
        or
        exists
        (
            GuardCondition gc, Expr left, Expr right |
            gc.controls(clobberWorld.getBasicBlock(), false)
            // gc.ensuresEq(left, right, 0, clobberWorld.getBasicBlock(), false)
            and
            (
                exists
                (
                    UseKindExpr useKind | 
                    gc.getAChild*() = useKind
                    and
                    "child1" = useKind.getChildNum()
                    and
                    result = useKind.getComparedToType()
                )
                or
                exists
                (
                    BinaryUseKindExpr binaryUseKind | 
                    gc.getAChild*() = binaryUseKind
                    and
                    "child1" = binaryUseKind.getChildNum()
                    and
                    result = binaryUseKind.getComparedToType()
                )
                or
                exists
                (
                    IsBinaryUseKind isBinaryUseKind | 
                    gc.getAChild*() = isBinaryUseKind
                    and
                    "child1" = isBinaryUseKind.getChildNum()
                    and
                    result = isBinaryUseKind.getComparedToType()
                )
            )
        )
    )
    else result = "NoLooseTypeFound"
}

string getLooseTypeForClobberWorldChild2(FunctionCall clobberWorld){
    // Extracting loose types from switch case
    if doesClobberMightHaveLooseTypesChild2(clobberWorld) = true
    then 
    (
        exists
        (
            SwitchStmt st, SwitchCase case | 
            st = getInnerSwitchStatement(clobberWorld, "useKind")
            and
            st.getExpr().(FunctionCall).getQualifier().(FunctionCall).getTarget().hasName("child2")
            and
            case.getSwitchStmt() = st
            and
            (
                not clobberWorld.getAPredecessor+() = case
            )
            and result = case.getExpr().toString()
        )
        or
        exists
        (
            SwitchStmt st, SwitchCase case | 
            st = getInnerSwitchStatement(clobberWorld, "binaryUseKind")
            and
            case.getSwitchStmt() = st
            and
            (
                not clobberWorld.getAPredecessor+() = case
            )
            and result = case.getExpr().toString()
        )
        or
        exists
        (
            GuardCondition gc, Expr left, Expr right |
            gc.controls(clobberWorld.getBasicBlock(), false)
            // gc.ensuresEq(left, right, 0, clobberWorld.getBasicBlock(), false)
            and
            (
                exists
                (
                    UseKindExpr useKind | 
                    gc.getAChild*() = useKind
                    and
                    "child2" = useKind.getChildNum()
                    and
                    result = useKind.getComparedToType()
                )
                or
                exists
                (
                    BinaryUseKindExpr binaryUseKind | 
                    gc.getAChild*() = binaryUseKind
                    and
                    "child2" = binaryUseKind.getChildNum()
                    and
                    result = binaryUseKind.getComparedToType()
                )
                or
                exists
                (
                    IsBinaryUseKind isBinaryUseKind | 
                    gc.getAChild*() = isBinaryUseKind
                    and
                    "child2" = isBinaryUseKind.getChildNum()
                    and
                    result = isBinaryUseKind.getComparedToType()
                )
            )
        )
    )
    else result = "NoLooseTypeFound"
}

string getLooseTypeForClobberWorldChild3(FunctionCall clobberWorld){
    // Extracting loose types from switch case
    if doesClobberMightHaveLooseTypesChild3(clobberWorld) = true
    then 
    (
        exists
        (
            SwitchStmt st, SwitchCase case | 
            st = getInnerSwitchStatement(clobberWorld, "useKind")
            and
            st.getExpr().(FunctionCall).getQualifier().(FunctionCall).getTarget().hasName("child3")
            and
            case.getSwitchStmt() = st
            and
            (
                not clobberWorld.getAPredecessor+() = case
            )
            and result = case.getExpr().toString()
        )
        or
        exists
        (
            GuardCondition gc, Expr left, Expr right |
            gc.controls(clobberWorld.getBasicBlock(), false)
            // gc.ensuresEq(left, right, 0, clobberWorld.getBasicBlock(), false)
            and
            (
                exists
                (
                    UseKindExpr useKind | 
                    gc.getAChild*() = useKind
                    and
                    "child3" = useKind.getChildNum()
                    and
                    result = useKind.getComparedToType()
                )
            )
        )
    )
    else result = "NoLooseTypeFound"
}

predicate getStrictTypeConstraints(FunctionCall clobberWorld, string strictTypeOfChild1, string strictTypeOfChild2, string strictTypeOfChild3){
    strictTypeOfChild1 = getStrictTypeForClobberWorldChild1(clobberWorld)
    and
    strictTypeOfChild2 = getStrictTypeForClobberWorldChild2(clobberWorld)
    and
    strictTypeOfChild3 = getStrictTypeForClobberWorldChild3(clobberWorld) 
}

predicate getLooseTypeConstraints(FunctionCall clobberWorld, string looseTypeOfChild1, string looseTypeOfChild2, string looseTypeOfChild3){
    looseTypeOfChild1 = getLooseTypeForClobberWorldChild1(clobberWorld)
    and
    looseTypeOfChild2 = getLooseTypeForClobberWorldChild2(clobberWorld)
    and
    looseTypeOfChild3 = getLooseTypeForClobberWorldChild3(clobberWorld) 
}

Function findToPrimitveCall(Function target) {
    exists(FunctionCall call |
    call.getEnclosingFunction() = target and
    call.getTarget() = result
    )
}
    
Function findToPrimitveCalls(Function function) {
    (
        result = function
        and
        result.getName().matches("%toPrimitive%")
    )
    or
    exists
    (
        Function diveIn |
        diveIn = findToPrimitveCall(function) and
        result = findToPrimitveCalls(diveIn)
    )
}

Function findToMethodTableCalls(Function function) {
    (
        result = function
        and
        result.getName().matches("%methodTable")
    )
    or
    exists
    (
        Function diveIn |
        diveIn = findToPrimitveCall(function) and
        result = findToMethodTableCalls(diveIn)
    )
}