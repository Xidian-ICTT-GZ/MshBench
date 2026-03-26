import javacard.framework.*;

class Program {
    static short abs(short x)
    //@ requires true;
    //@ ensures result == (x == -32768 ? 0 : (x < 0 ? -x : x));
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