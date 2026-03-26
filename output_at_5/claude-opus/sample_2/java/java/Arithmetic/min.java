class Program {
    static short min(short x, short y, short z)
        //@ requires true;
        //@ ensures true;
    {
        short m = x < y ? x : y;
        m = m < z ? m : z;
        return m;
    }
}