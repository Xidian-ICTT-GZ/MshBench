class Program {
    //@ requires true;
    //@ ensures true;
    static short abs(short x)
        
        
    {
        if (x < 0) {
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}