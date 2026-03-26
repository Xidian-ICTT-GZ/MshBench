class Program {
    static int abs(short x)
    //@ requires x != Short.MIN_VALUE;
    //@ ensures 0 <= result;
    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}