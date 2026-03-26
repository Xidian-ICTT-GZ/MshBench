class Program {
    static short abs(short x)
        //@ requires true;
        //@ ensures (x != Short.MIN_VALUE ? result == (x < 0 ? (short)-x : x) : result == x);
    {
        if (x < 0) {
            //@ assert x != Short.MIN_VALUE; 
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}