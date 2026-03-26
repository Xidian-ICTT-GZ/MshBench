class Program {
    static short abs(short x)
    //@ requires true;
    //@ ensures (result == x || (result == (short)-x && x < 0)) && (result >= 0) && (result <= 32767);
    {
        if (x < 0) {
            //@ assert x > Short.MIN_VALUE; // to avoid overflow in -x
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}