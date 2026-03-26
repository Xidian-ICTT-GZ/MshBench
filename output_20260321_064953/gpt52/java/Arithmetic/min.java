class Program {
    //@ requires true;
    //@ ensures true;
    static short min(short x, short y, short z)
        
        

    {
        short m = x < y ? x : y;
        m = m < z ? m : z;
        return m;
    }
}