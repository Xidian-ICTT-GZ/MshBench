class Program {
    //@ requires true;
    //@ ensures result >= 0;
    static short abs(short x)
        
        
    {
        //@ close Program_abs_ghost();
        if (x < 0) {
            x = (short)-x;
            //@ open Program_abs_ghost();
            //@ assert x >= 0;
            return x;
        } else {
            //@ open Program_abs_ghost();
            //@ assert x >= 0;
            return x;
        }
    }

    //@ predicate Program_abs_ghost() = true;
}