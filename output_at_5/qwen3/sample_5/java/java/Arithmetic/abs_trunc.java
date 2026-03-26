class Program {
    static short abs(short x)
        //@ requires true;
        //@ ensures result == (x < 0 ? -x : x);
        
    {
        if (x < 0) {
            if (x != Short.MIN_VALUE) {
                x = (short)-x;
                return x;
            } else {
                return x;
            }
        } else {
            return x;
        }
    }
}