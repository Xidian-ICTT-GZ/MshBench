class Program {
    /*@
    predicate abs_result(short x, short result) = (x >= 0 ? result == x : result == -x) &*& result >= 0;
    @*/

    static short abs(short x)
    //@ requires true;
    //@ ensures abs_result(x, result);
    {
        if (x < 0) {
            x = (short)-x;
            //@ close abs_result(old_x, x);
            return x;
        } else {
            //@ close abs_result(x, x);
            return x;
        }
    }
}