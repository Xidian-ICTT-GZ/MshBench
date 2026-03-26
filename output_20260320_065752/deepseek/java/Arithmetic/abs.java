class Program {
    //@ requires true;
    //@ ensures true;
    static int abs(short x)
        
        
    {
        //@ assert x >= -32768 &*& x <= 32767;
        if (x < 0)
            //@ assert x < 0;
            return -x;
        else
            //@ assert x >= 0;
            return x;
    }
}