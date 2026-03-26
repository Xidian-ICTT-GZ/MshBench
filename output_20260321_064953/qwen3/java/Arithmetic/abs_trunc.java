class Program {
    /*@
    predicate program_inv() = true;
    @*/

    //@ requires true;
    //@ ensures result >= 0 &*& (x >= 0 ? result == x : result == -x);
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