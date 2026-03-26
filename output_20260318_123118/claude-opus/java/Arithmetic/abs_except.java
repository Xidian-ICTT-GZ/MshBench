import javacard.framework.*;

class Program {
    /*@ predicate abs_parameter(short x) = true; @*/
    
    //@ requires abs_parameter(x) &*& x != Short.MIN_VALUE;
    //@ ensures result >= 0 &*& (result == (x < 0 ? (short)-x : x));
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