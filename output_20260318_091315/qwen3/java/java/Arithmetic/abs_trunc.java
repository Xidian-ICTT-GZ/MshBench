class Program {
    /*@ predicate true_pred() = true; @*/

    //@ requires true &*& x >= -32768 &*& x <= 32767;
    //@ ensures result >= 0 &*& result <= 32767 &*& (x >= 0 ==> result == x) &*& (x < 0 ==> result == -x);
    static short abs(short x)
        
        
    {
        if (x < 0) {
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}