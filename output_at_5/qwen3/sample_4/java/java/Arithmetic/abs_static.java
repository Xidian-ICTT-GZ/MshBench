class Program {
    static short abs(short x)
        //@ requires true;
        //@ ensures result == (x < 0 ? -x : x);
        
    {
        if (x < 0) {
            x = (short)-x;
            //@ assert x >= 0;
            return x;
        } else {
            return x;
        }
    }
}