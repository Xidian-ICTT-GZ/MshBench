class Program {
    static short abs(short x)
    //@ requires x != -32768;
    //@ ensures true;
        
        
    {
        if (x < 0) {
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}