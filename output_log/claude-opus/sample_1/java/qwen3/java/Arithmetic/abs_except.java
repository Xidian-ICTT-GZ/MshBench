import javacard.framework.*;

class Program {
    /*@ predicate abs_arg(short x) = x != -32768; @*/

    static short abs(short x)
    //@ requires abs_arg(x);
    //@ ensures (result == (x < 0 ? (short)(-x) : x));
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