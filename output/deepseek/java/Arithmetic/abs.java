class Program {
    //@ requires true;
    //@ ensures result >= 0 &*& (x >= 0 ? result == x : result == -x);
    static int abs(short x)

    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}