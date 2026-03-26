import javacard.framework.*;

class Program {
    static short abs(short x)
    //@ requires x != (short)-32768;
    //@ ensures result == (x < 0 ? (short)(-x) : x);

    {
        if (x == -32768)
            ISOException.throwIt(ISO7816.SW_UNKNOWN);
        if (x < 0) {
            x = (short) -x;
            return x;
        } else {
            return x;
        }
    }
}