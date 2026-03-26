class Program {
    static int abs(short x)
        //@ requires true;
        //@ ensures result == (x < 0 ? -x : x);
    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}