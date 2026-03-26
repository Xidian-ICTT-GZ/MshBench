import javacard.framework.*;

class Program {
    //@ requires -32767 <= x &*& x <= 32767;
    //@ ensures 0 <= result &*& result <= 32767;
    static short abs(short x)
        
        
    {
        //@ open [-32767..32767](x);
        if (x == -32768)
            ISOException.throwIt(ISO7816.SW_UNKNOWN);
        //@ close [-32767..32767](x);
        if (x < 0) {
            //@ close [-32767..32767](x);
            //@ open [-32767..32767](x);
            //@ assert x < 0;
            //@ close [0..32767](-x);
            x = (short)-x;
            //@ open [0..32767](x);
            return x;
        } else {
            //@ close [-32767..32767](x);
            //@ open [-32767..32767](x);
            //@ assert 0 <= x;
            //@ close [0..32767](x);
            return x;
        }
    }
}

/*@
predicate [-32767..32767](short v) = -32767 <= v &*& v <= 32767;
predicate [0..32767](short v) = 0 <= v &*& v <= 32767;
@*/