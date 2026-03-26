class Program {
    //@ requires true;
    //@ ensures 0 <= result;
    static short abs(short x)
        
        
    {
        //@ open emp();
        if (x < 0) {
            x = (short)-x;
            //@ close emp();
            return x;
        } else {
            //@ close emp();
            return x;
        }
    }
}