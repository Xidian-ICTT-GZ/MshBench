class Program {
    static short abs(short x)
        //@ requires x != Short.MIN_VALUE;
        //@ ensures result == (x < 0 ? -x : x);
        
    {
        if (x < 0) {
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}