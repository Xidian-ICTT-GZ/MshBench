import javacard.framework.*;

class Program {
    static short abs(short x)
        //@ requires true;
        //@ ensures (x == -32768 ? false : true);
        
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