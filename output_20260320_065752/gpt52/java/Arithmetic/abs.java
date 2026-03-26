class Program {
    //@ requires true;
    //@ ensures true;
    static int abs(short x)
        
        
    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}