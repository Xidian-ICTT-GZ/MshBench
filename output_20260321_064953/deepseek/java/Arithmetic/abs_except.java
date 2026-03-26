import javacard.framework.*;

class Program {
    //@ requires true;
    //@ ensures result >= 0;
    static short abs(short x)
        
        
    {
        //@ open System.out.println();
        if (x == -32768)
            ISOException.throwIt(ISO7816.SW_UNKNOWN);
        //@ assert x != -32768;
        if (x < 0) {
            //@ assert x < 0;
            x = (short)-x;
            //@ assert x == - \old(x);
            //@ assert x > 0;
            return x;
        } else {
            //@ assert x >= 0;
            return x;
        }
    }
}