class Program {
    //@ requires true;
    //@ ensures result >= 0;
    //@ ensures (x < 0 ==> result == -x) &*& (x >= 0 ==> result == x);
    static int abs(short x)
        
        
    {
        //@ assert true;
        if (x < 0)
            //@ assert x < 0;
            return -x;
        else
            //@ assert x >= 0;
            return x;
    }
}