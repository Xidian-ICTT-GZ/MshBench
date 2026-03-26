class Program {
    //@ requires true;
    //@ ensures true;
    static short min(short x, short y, short z)
        
        

    {
        //@ assert true;
        short m = x < y ? x : y;
        //@ assert true;
        m = m < z ? m : z;
        //@ assert true;
        return m;
    }
}