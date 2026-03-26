class Program {
    static short abs(short x)
        //@ requires true;
        //@ ensures result >= 0;
    {
        if (x < 0) {
            x = (short) -x;
            return x;
        } else {
            return x;
        }
    }
}