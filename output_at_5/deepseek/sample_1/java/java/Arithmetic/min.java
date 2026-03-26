class Program {
    //@ requires true;
    //@ ensures true;
    static short min(short x, short y, short z)
        
        

    {
        short m = x < y ? x : y;
        //@ assert m == (x < y ? x : y);
        m = m < z ? m : z;
        //@ assert m == (m < z ? m : z);
        return m;
    }
}