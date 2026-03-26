class Program {
    //@ requires true;
    //@ ensures 0 <= result;
    static short abs(short x)
        
        
    {
        //@ close exists(0);
        if (x < 0) {
            x = (short)-x;
            //@ assert 0 <= x;
            //@ close exists(0);
            return x;
        } else {
            //@ assert 0 <= x;
            //@ close exists(0);
            return x;
        }
    }
}