import javacard.framework.*;

class Program {
    //@ requires -32767 <= x &*& x <= 32767;
    //@ ensures 0 <= result &*& result <= 32767;
    static short abs(short x)
    {
        if (x == -32768)
            ISOException.throwIt(ISO7816.SW_UNKNOWN);
        //@ assert -32767 <= x &*& x <= 32767;
        if (x < 0) {
            //@ assert x < 0;
            //@ assert -32767 <= x &*& x <= -1;
            x = (short) -x;
            //@ assert 1 <= x &*& x <= 32767;
            return x;
        } else {
            //@ assert 0 <= x &*& x <= 32767;
            return x;
        }
    }
}