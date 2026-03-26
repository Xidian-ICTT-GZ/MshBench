class Program {
    static int abs(short x)
    //@ requires true;
    //@ ensures result >= 0;
    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}