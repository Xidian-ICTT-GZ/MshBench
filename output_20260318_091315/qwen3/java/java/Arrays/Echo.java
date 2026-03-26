package echo;

import javacard.framework.*;

/*@ predicate applet_state(Echo e; ) = true; @*/

public class Echo extends Applet {
    
    private static final byte Echo_CLA = (byte) 0xB0;
    private static final byte Echo_INS = (byte) 0x01;
    
    //@ requires bArray != null &*& 0 <= bOffset &*& bOffset + bLength <= bArray.length;
    //@ ensures true;
    public static void install(byte[] bArray, short bOffset, byte bLength) 
    {
        Echo echo = new Echo();
        /*@ close applet_state(echo); @*/
        echo.register();
    }
    
    //@ requires this |-> _ &*& apdu |-> _;
    //@ ensures this |-> _ &*& apdu |-> _;
    public void process(APDU apdu) 
    {
        byte[] buffer = apdu.getBuffer();
        //@ assume buffer != null;
        
        if(selectingApplet())
            return;
        
        if(buffer[ISO7816.OFFSET_CLA] != Echo_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
        if(buffer[ISO7816.OFFSET_INS] != Echo_INS)
            ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        else
            echo(apdu);
    }
    
    //@ requires this |-> _ &*& apdu |-> _;
    //@ ensures this |-> _ &*& apdu |-> _;
    private void echo(APDU apdu)
    {
        byte[] buffer = apdu.getBuffer();
        //@ assume buffer != null;
        //@ assume 0 <= ISO7816.OFFSET_LC &*& ISO7816.OFFSET_LC < buffer.length;
        //@ assume 0 <= ISO7816.OFFSET_CDATA &*& ISO7816.OFFSET_CDATA < buffer.length;
        //@ assume (short)(buffer[ISO7816.OFFSET_CDATA] + buffer[ISO7816.OFFSET_LC]) >= 0;
        //@ assume (short)(buffer[ISO7816.OFFSET_CDATA] + buffer[ISO7816.OFFSET_LC]) <= buffer.length;
        
        apdu.setOutgoing();
        apdu.setOutgoingLength(buffer[ISO7816.OFFSET_LC]);
        apdu.sendBytes((short)buffer[ISO7816.OFFSET_CDATA], (short)(buffer[ISO7816.OFFSET_CDATA] + buffer[ISO7816.OFFSET_LC]));
    }
    
}