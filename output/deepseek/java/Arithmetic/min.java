class Program {
    //@ requires true;
    //@ ensures result == x || result == y || result == z;
    //@ ensures result <= x &*& result <= y &*& result <= z;
    static short min(short x, short y, short z)

    {
        short m = x < y ? x : y;
        //@ assert m == x || m == y;
        //@ assert m <= x &*& m <= y;
        m = m < z ? m : z;
        //@ assert m == x || m == y || m == z;
        //@ assert m <= x &*& m <= y &*& m <= z;
        return m;
    }
}