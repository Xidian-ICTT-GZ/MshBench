class Program {
    static short abs(short x)
        //@ requires true;
        //@ ensures result == (x < 0 ? (short)-x : x);
    {
        if (x < 0) {
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}