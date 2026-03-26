import javacard.framework.*;

class Program {
    /*@ predicate valid_short(short x) = -32768 <= x &*& x <= 32767; @*/

    //@ requires valid_short(x);
    //@ ensures valid_short(result) &*& result >= 0;
    static short abs(short x)
    {
        if (x == -32768)
            ISOException.throwIt(ISO7816.SW_UNKNOWN);
        if (x < 0) {
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}