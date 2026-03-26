class Program {
    //@ requires true;
    //@ ensures 0 <= result;
    static short abs(short x)
        
        
    {
        //@ close ProgramPred();
        if (x < 0) {
            x = (short)-x;
            //@ open ProgramPred();
            return x;
        } else {
            //@ open ProgramPred();
            return x;
        }
    }

    //@ predicate ProgramPred() = true;
}