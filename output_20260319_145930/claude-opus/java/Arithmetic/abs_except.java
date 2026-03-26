import javacard.framework.*;

class Program {
    static short abs(short x)
        //@ requires true;
        //@ ensures x != -32768 &*& (x >= 0 ? result == x : result == (short)-x) &*& result >= 0;
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