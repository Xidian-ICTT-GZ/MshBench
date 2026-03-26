class Program {
    //@ requires true;
    //@ ensures 0 <= result;
    static int abs(short x)
        
        
    {
        //@ open true;
        if (x < 0)
            //@ close true;
            return -x;
        else
            //@ close true;
            return x;
    }
}