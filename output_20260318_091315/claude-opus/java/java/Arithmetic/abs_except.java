import javacard.framework.*;

class Program {
    /*@ predicate abs_arg(short x) = true; @*/
    //@ requires abs_arg(x);
    //@ ensures abs_arg(result) &*& (result >= 0);
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