import cpp
import semmle.code.cpp.controlflow.Guards


// DfgCallOperation helper functions

// Extracting the type could be from an if statement or a switch case
// Verifying the type can be done by several functions (This are the main ones, there are possibly more):
// 1) node->childx()->useKind() == someType
// 2) node->binaryUseKind() == someType (This compares child 1 and 2 of node)
// 3) node->isBinaryUseKind(someType)
// 4) switch(node->childx()->useKind())
// 5) switch(node->binaryUseKind())

class UseKindExpr extends ComparisonOperation{
    string comparedType;
    string childNum;

    UseKindExpr(){
        exists
        (
            FunctionCall useKind | 
            useKind.getTarget().hasName("useKind")
            and
            this.getAChild() = useKind
            and
            childNum = useKind.getQualifier().(FunctionCall).getTarget().getName()
            and
            if useKind = this.getLeftOperand()
            then (comparedType = this.getRightOperand().toString())
            else comparedType = this.getLeftOperand().toString()
        )
    }

    string getChildNum(){
        result = childNum
    }

    string getComparedToType(){
        result = comparedType
    }
}

class BinaryUseKindExpr extends ComparisonOperation{
    string comparedType;
    string childNum;

    BinaryUseKindExpr(){
        exists
        (
            FunctionCall binaryUseKind | 
            binaryUseKind.getTarget().hasName("binaryUseKind")
            and
            this.getAChild() = binaryUseKind
            and
            if binaryUseKind = this.getLeftOperand()
            then (comparedType = this.getRightOperand().toString())
            else comparedType = this.getLeftOperand().toString()
        )
        and
        (
            childNum = "child1"
            or
            childNum = "child2"
        )
    }

    string getChildNum(){
        result = childNum
    }

    string getComparedToType(){
        result = comparedType
    }
}

class IsBinaryUseKind extends FunctionCall{
    string comparedType; 
    string childNum;

    IsBinaryUseKind(){
        this.getTarget().hasName("isBinaryUseKind")
        and
        comparedType = this.getArgument(0).toString()
        and
        (
            childNum = "child1"
            or
            childNum = "child2"
        )
    }

    string getChildNum(){
        result = childNum
    }

    string getComparedToType(){
        result = comparedType
    }
}
