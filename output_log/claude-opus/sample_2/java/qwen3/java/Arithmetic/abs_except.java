import javacard.framework.*;

class Program {
    /*@
    predicate valid_short(short x) = (
        true
    );
    @*/

    static short abs(short x)
    //@ requires valid_short(x);
    /*@ 
      ensures
          (x == -32768 ==> false) &*&
          (x != -32768 ==>
            (x < 0 ==> result == -x) &*&
            (x >= 0 ==> result == x));
    @*/
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