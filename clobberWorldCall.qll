import cpp
import helperFunctions

class ClobberWorldCall extends FunctionCall{
    
    string opCode;
    string strictTypeConstraintsNode1;
    string strictTypeConstraintsNode2;
    string strictTypeConstraintsNode3;
    string looseTypeConstraintsNode1;
    string looseTypeConstraintsNode2;
    string looseTypeConstraintsNode3;
    // string operandType;

    ClobberWorldCall()
    {
        this.getTarget().hasName("clobberWorld")
        and
        exists
        (
            Function executeEffects |
            executeEffects.hasName("executeEffects")
            and
            this.getEnclosingFunction() = executeEffects
        )
        
        and
        // Extracting the op code for each call
        opCode = getOpForClobberWorld(this)
        and

        // Extracting the strict and loose types
        getStrictTypeConstraints(this, strictTypeConstraintsNode1, strictTypeConstraintsNode2, strictTypeConstraintsNode3)
        and
        getLooseTypeConstraints(this, looseTypeConstraintsNode1, looseTypeConstraintsNode2, looseTypeConstraintsNode3)

    }

    string getAnOpCode(){
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