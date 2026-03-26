class Program {
    //@ requires true;
    //@ ensures result == (x < 0 ? -x : x);
    static int abs(short x)
        
        
    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}