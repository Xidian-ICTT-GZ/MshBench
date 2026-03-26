class Program {
    //@ requires x > -32768;
    //@ ensures (x < 0 ==> result == -x) &*& (x >= 0 ==> result == x);
    static int abs(short x)
    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}