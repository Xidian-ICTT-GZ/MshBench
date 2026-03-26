class Program {
    static short abs(short x)
        //@ requires true;
        //@ ensures result == (x < 0 ? -x : x);
        
    {
        if (x < 0) {
            // Special case for Short.MIN_VALUE to avoid overflow during negation
            if (x == -32768) {
                return -32768;
            }
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}