class Program {
    static short min(short x, short y, short z)
        //@ requires true;
        //@ ensures result == (x < y ? (m = x : y) : m = y);
    {
        short m = x < y ? x : y;
        m = m < z ? m : z;
        return m;
    }
}