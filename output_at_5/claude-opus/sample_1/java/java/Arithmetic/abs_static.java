class Program {
    /*@
    predicate abs_arg(short x) = true;
    @*/
    static short abs(short x)
    //@ requires abs_arg(x);
    //@ ensures abs_arg(result);
    {
        if (x < 0) {
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}