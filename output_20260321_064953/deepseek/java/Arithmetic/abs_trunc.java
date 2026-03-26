class Program {
    //@ requires true;
    //@ ensures 0 <= result;
    static short abs(short x)
        
        
    {
        //@ close Program_abs_ghost(x);
        if (x < 0) {
            x = (short)-x;
            //@ open Program_abs_ghost(_);
            //@ assert 0 <= x;
            return x;
        } else {
            //@ open Program_abs_ghost(_);
            //@ assert 0 <= x;
            return x;
        }
    }

    /*@
    predicate Program_abs_ghost(short x) = true;
    @*/
}