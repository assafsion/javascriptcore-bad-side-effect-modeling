import cpp
import helperFunctions
import semmle.code.cpp.dataflow.TaintTracking
import dfgOperation

predicate isJsObject(Variable var){
    var.getType().toString() = "JSObject *"
  }

  Function getFunctionWrapper(Function target) {
    exists(FunctionCall call |
    call = target.getACallToThisFunction() and
    call.getEnclosingFunction() = result
    )
}
    
    Function getFunctionWrappers(Function function) {
    result = function
    or
    exists(Function wrapper |
    wrapper = getFunctionWrapper(function) and
    result = getFunctionWrappers(wrapper)
    )
}

// This query finds all JS operations that cause side effects when using a ProxyObject
// And
// The DFG JIT compiler won't call clobberWorld() 
from FunctionCall fc, VariableAccess jsObjectAccess, Parameter source, DfgOperation operation,  Expr asObjArg, Function compareTo
where 
  isJsObject(jsObjectAccess.getTarget())
  and 
  fc.getQualifier() = jsObjectAccess
  and
  exists
  (
    Function fromProxy |
    fromProxy.getParentScope().toString() = "ProxyObject"
    and
    compareTo.getName() = fromProxy.getName()
    and
    fc.getTarget() = getFunctionWrappers(compareTo)
  )
  and
  (
    operation.hasACallToClobberWorld() = true
    and 
    exists
    (
        ClobberWorldCall clobberWorldCall |
        clobberWorldCall.getAnOpCode() = operation.getOpcode()
        and
        not exists
        (
          |  operation.getNode1StrictConstraints() = clobberWorldCall.getNode1StrictConstraints()
        )
    )
  )
  and
  operation.getAParameter() = source
  and
  exists
  (
    LinkOperationToExecVM config, FunctionCall asObject, ConvertToObjectAndCall config2| 
        (
          (
            asObject.getTarget().hasName("asObject")
            or
            asObject.getTarget().hasName("toObject")
          )
          and
          asObject.getAnArgument() = asObjArg
          and
          config.hasFlow(DataFlow::parameterNode(source), DataFlow::exprNode(asObjArg))
          and
          config2.hasFlow(DataFlow::exprNode(asObject), DataFlow::exprNode(jsObjectAccess))
        )
        or
        (
          asObjArg = jsObjectAccess.getTarget().getAnAccess()
          and
          config.hasFlow(DataFlow::parameterNode(source), DataFlow::exprNode(asObjArg))
        )
  )
select operation, source, fc, compareTo