class Program {
    /*@
    predicate min_args(short x, short y, short z) = true;
    @*/
    static short min(short x, short y, short z)
        //@ requires min_args(x, y, z);
        //@ ensures min_args(x, y, z) &*& result <= x &*& result <= y &*& result <= z;
    {
        short m = x < y ? x : y;
        m = m < z ? m : z;
        return m;
    }
}