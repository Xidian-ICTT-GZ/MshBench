class Program {
    //@ requires x > (short)-32768;
    //@ ensures result >= 0;
    static int abs(short x)
    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}