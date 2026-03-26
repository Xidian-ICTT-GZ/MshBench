class Program {
    static short min(short x, short y, short z)
        //@ requires true;
        //@ ensures result == (x < y ? x : y) < z ? (x < y ? x : y) : z;
    {
        short m = x < y ? x : y;
        m = m < z ? m : z;
        return m;
    }
}