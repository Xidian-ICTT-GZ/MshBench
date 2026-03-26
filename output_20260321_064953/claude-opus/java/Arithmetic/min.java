class Program {
    /*@
    predicate valid_short(short x) = true;
    @*/
    //@ requires true;
    //@ ensures true &*& result == (x < y ? (x < z ? x : z) : (y < z ? y : z));
    static short min(short x, short y, short z)
    {
        short m = x < y ? x : y;
        m = m < z ? m : z;
        return m;
    }
}