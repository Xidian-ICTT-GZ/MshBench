class Program {
    //@ requires true;
    //@ ensures 0 <= result;
    static int abs(short x)
        
        
    {
        //@ close_invariant();
        if (x < 0)
            //@ close_invariant();
            return -x;
        else
            //@ close_invariant();
            return x;
    }
}