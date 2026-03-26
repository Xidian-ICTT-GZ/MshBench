class Program {
    /*@
    predicate dummy() = true;
    @*/
    
    //@ requires true;
    //@ ensures result >= 0;
    static int abs(short x)
        
        
    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}