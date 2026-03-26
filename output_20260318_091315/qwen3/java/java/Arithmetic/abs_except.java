import javacard.framework.*;

class Program {
    /*@ predicate valid_short(short x) = true; @*/

    //@ requires valid_short(x);
    //@ ensures (x == -32768) ==> false &*& result == 0;
    //@ ensures (x != -32768) &*& (x < 0) ==> result == -x &*& valid_short(result);
    //@ ensures (x != -32768) &*& (x >= 0) ==> result == x &*& valid_short(result);
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