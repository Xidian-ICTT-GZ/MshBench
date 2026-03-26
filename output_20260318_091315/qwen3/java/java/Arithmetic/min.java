class Program {
    /*@ predicate true_pred() = true; @*/

    //@ requires true &*& true;
    //@ ensures result == x || result == y || result == z &*&
    
    static short min(short x, short y, short z) {
        short m = x < y ? x : y;
        m = m < z ? m : z;
        return m;
    }
}