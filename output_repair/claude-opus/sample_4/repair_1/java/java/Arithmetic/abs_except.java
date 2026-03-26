import javacard.framework.*;

class Program {
    //@ requires x != -32768 || x == -32768;
    //@ ensures result >= 0;
    static short abs(short x)
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