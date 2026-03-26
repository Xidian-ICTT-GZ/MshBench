class Program {
    /*@
    predicate valid_short(int x) = x >= -32768 &*& x <= 32767;
    @*/
    
    static short abs(short x)
        //@ requires true;
        //@ ensures valid_short(result);
        //@ ensures result == (x < 0 ? (short)-x : x);
    {
        if (x < 0) {
            //@ assert valid_short(x);
            // To avoid overflow, special-case Short.MIN_VALUE which cannot be negated in short:
            if (x == Short.MIN_VALUE) {
                return Short.MIN_VALUE;
            }
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}