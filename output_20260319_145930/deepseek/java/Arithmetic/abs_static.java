class Program {
    //@ requires true;
    //@ ensures result >= 0;
    //@ ensures x >= 0 ? result == x : result == (short)-x;
    static short abs(short x)
        
        
    {
        //@ assert true;
        if (x < 0) {
            x = (short)-x;
            //@ assert x >= 0;
            return x;
        } else {
            //@ assert x >= 0;
            return x;
        }
    }
}