class Program {
    //@ requires true;
    //@ ensures 0 <= result;
    static short abs(short x)
        
        
    {
        //@ close Program_abs_ghost();
        if (x < 0) {
            x = (short)-x;
            //@ open Program_abs_ghost();
            return x;
        } else {
            //@ open Program_abs_ghost();
            return x;
        }
    }
    
    /*@
    predicate Program_abs_ghost() = true;
    @*/
}