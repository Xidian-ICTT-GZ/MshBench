class Program {
    static int abs(short x)
        //@ requires true;
        //@ ensures result >= 0 &*& (result == x || result == -x);
    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}
