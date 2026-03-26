class Program {
    /*@
    predicate abs(int x) = true;
    @*/

    static int abs(short x)
        //@ requires true;
        //@ ensures true;
    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}