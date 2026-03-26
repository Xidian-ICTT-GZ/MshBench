class Program {
    /*@
    predicate abs_param(short x) = true;
    @*/
    static short abs(short x)
        //@ requires abs_param(x);
        //@ ensures abs_param(result) &*& 0 <= result;
    {
        if (x < 0) {
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}