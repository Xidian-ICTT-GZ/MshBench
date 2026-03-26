class Program {
    /*@
    predicate abs_result(int x, int result) = (x >= 0 ? result == x : result == -x);
    @*/
    
    static int abs(short x)
    //@ requires true;
    //@ ensures abs_result(x, result);
    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}