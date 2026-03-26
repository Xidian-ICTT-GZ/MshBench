class Program {
    static short min(short x, short y, short z)
        //@ requires true;
        //@ ensures result == m(x, y, z);
        /*@
        predicate boolEq(short a, short b) = a == b;
        @*/
    {
        short m = x < y ? x : y;
        m = m < z ? m : z;
        return m;
    }
}