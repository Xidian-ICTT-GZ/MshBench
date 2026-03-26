package echo;

import javacard.framework.*;

public class Echo extends Applet {
    
    private static final byte Echo_CLA = (byte) 0xB0;
    private static final byte Echo_INS = (byte) 0x01;
    
    //@ predicate apdu_buffer(byte[] buffer) = buffer != null &*& buffer.length >= 15;
    
    //@ requires bArray != null &*& 0 <= bOffset &*& bOffset + bLength <= bArray.length;
    //@ ensures true;
    public static void install(byte[] bArray, short bOffset, byte bLength) 
    {
        Echo echo = new Echo();
        echo.register();
    }
    
    //@ requires apdu != null &*& apdu.getBuffer() != null &*& apdu.getBuffer().length >= 15;
    //@ ensures true;
    public void process(APDU apdu) 
    {
        byte[] buffer = apdu.getBuffer();
        
        if(selectingApplet())
            return;
        
        //@ assert apdu_buffer(buffer);
        if(buffer[ISO7816.OFFSET_CLA] != Echo_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
        if(buffer[ISO7816.OFFSET_INS] != Echo_INS)
            ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        else
            echo(apdu);
    }
    
    //@ requires apdu != null &*& apdu.getBuffer() != null &*& apdu.getBuffer().length >= 15 &*& 0 <= (short)apdu.getBuffer()[ISO7816.OFFSET_LC];
    //@ ensures true;
    private void echo(APDU apdu)
    {
        byte[] buffer = apdu.getBuffer();
        apdu.setOutgoing();
        
        apdu.setOutgoingLength(buffer[ISO7816.OFFSET_LC]);
        
        //@ assert 0 <= (short)buffer[ISO7816.OFFSET_CDATA];
        //@ assert 0 <= (short)buffer[ISO7816.OFFSET_LC];
        apdu.sendBytes((short)buffer[ISO7816.OFFSET_CDATA], (short)(buffer[ISO7816.OFFSET_CDATA] + buffer[ISO7816.OFFSET_LC]));
    }
}