class Program {
    static short min(short x, short y, short z)
        //@ requires true;
        /*@
        ensures
            result <= x && result <= y && result <= z &&
            (result == x || result == y || result == z);
        @*/
    {
        short m = x < y ? x : y;
        m = m < z ? m : z;
        return m;
    }
}
