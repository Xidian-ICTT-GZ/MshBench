import javacard.framework.*;

class Program {
    //@ requires -32767 <= x &*& x <= 32767;
    //@ ensures 0 <= result &*& result <= 32767;
    static short abs(short x)
        
        
    {
        //@ close [-32767,32767]ints(x, _);
        if (x == -32768)
            ISOException.throwIt(ISO7816.SW_UNKNOWN);
        //@ open [-32767,32767]ints(x, _);
        if (x < 0) {
            //@ close [-32767,32767]ints(x, _);
            x = (short)-x;
            //@ open [-32767,32767]ints(x, _);
            //@ assert 0 <= x;
            return x;
        } else {
            //@ assert 0 <= x;
            return x;
        }
    }
}

/*@
predicate [-32767,32767]ints(short v; short v0) =
    -32767 <= v &*& v <= 32767 &*& v0 == v;
@*/