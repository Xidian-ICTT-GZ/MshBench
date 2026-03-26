class Program {
    //@ requires true;
    //@ ensures 0 <= result;
    static short abs(short x)
        
        
    {
        //@ close exists(x);
        if (x < 0) {
            x = (short)-x;
            //@ assert 0 <= x;
            //@ open exists(x);
            return x;
        } else {
            //@ assert 0 <= x;
            //@ open exists(x);
            return x;
        }
    }
}