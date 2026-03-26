class Program {
    static int abs(short x)
        //@ requires true;
        //@ ensures (x < 0) ==> (result == -x) &*& (x >= 0) ==> (result == x);
    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}