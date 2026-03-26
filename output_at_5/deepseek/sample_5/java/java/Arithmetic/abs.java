class Program {
    //@ requires true;
    //@ ensures 0 <= result;
    static int abs(short x)
        
        
    {
        //@ assert x >= -32768 &*& x <= 32767;
        if (x < 0)
            //@ assert x < 0;
            //@ assert -x >= 0;
            return -x;
        else
            //@ assert x >= 0;
            return x;
    }
}