class Program {
    //@ requires true;
    //@ ensures result >= 0;
    static int abs(short x)
        
        
    {
        //@ close Program_abs_ghost();
        if (x < 0)
            //@ open Program_abs_ghost();
            return -x;
        else
            //@ open Program_abs_ghost();
            return x;
    }
    
    /*@
    predicate Program_abs_ghost() = true;
    @*/
}