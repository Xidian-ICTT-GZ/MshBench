class Program {
    //@ requires true;
    //@ ensures 0 <= result;
    static int abs(short x)
        
        
    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}