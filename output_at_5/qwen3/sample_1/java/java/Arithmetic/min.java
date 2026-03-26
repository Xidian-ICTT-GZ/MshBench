class Program {
    /*@
    predicate shortMin(short x, short y, short z) = true;
    @*/

    static short min(short x, short y, short z)
        //@ requires true;
        //@ ensures result == (x < y ? (m < z ? m : z) : (y < z ? y : z));
    {
        short m = x < y ? x : y;
        m = m < z ? m : z;
        return m;
    }
}