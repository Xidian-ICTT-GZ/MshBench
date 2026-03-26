import javacard.framework.*;

class Program {
    /*@ predicate abs_argument(short x) = x != -32768; @*/

    static short abs(short x)
    //@ requires abs_argument(x);
    //@ ensures result >= 0 &*& (result == x || result == -x);
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