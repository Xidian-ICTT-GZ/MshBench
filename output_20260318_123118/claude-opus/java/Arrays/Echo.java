package echo;

import javacard.framework.*;

public class Echo extends Applet {
    
    private static final byte Echo_CLA = (byte) 0xB0;
    private static final byte Echo_INS = (byte) 0x01;
    
    //@ predicate apdu_buffer(byte[] buffer, int length) = buffer != null &*& 0 <= length &*& length <= buffer.length;
    
    //@ requires bArray != null &*& bOffset >= 0 &*& bLength >= 0 &*& bOffset + bLength <= bArray.length;
    //@ ensures true;
    public static void install(byte[] bArray, short bOffset, byte bLength) 
    {
        Echo echo = new Echo();
        echo.register();
    }
    
    //@ requires apdu != null &*& apdu.getBuffer() != null;
    //@ ensures true;
    public void process(APDU apdu) 
    {
        byte[] buffer = apdu.getBuffer();
        //@ open apdu_buffer(buffer, buffer.length);
        //@ assert buffer != null;
        if(selectingApplet())
            return;
        
        //@ assume buffer.length > ISO7816.OFFSET_CLA;
        if(buffer[ISO7816.OFFSET_CLA] != Echo_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
        //@ assume buffer.length > ISO7816.OFFSET_INS;
        if(buffer[ISO7816.OFFSET_INS] != Echo_INS)
            ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        else
            echo(apdu);
    }
    
    //@ requires apdu != null &*& apdu.getBuffer() != null;
    //@ requires apdu.getBuffer().length > ISO7816.OFFSET_LC &*& apdu.getBuffer()[ISO7816.OFFSET_LC] >= 0 &*& 
    //@          apdu.getBuffer().length > ISO7816.OFFSET_CDATA + apdu.getBuffer()[ISO7816.OFFSET_LC];
    //@ ensures true;
    private void echo(APDU apdu)
    {
        byte[] buffer = apdu.getBuffer();
        //@ open apdu_buffer(buffer, buffer.length);
        apdu.setOutgoing();
        apdu.setOutgoingLength(buffer[ISO7816.OFFSET_LC]);
        apdu.sendBytes((short)buffer[ISO7816.OFFSET_CDATA], 
                       (short)(buffer[ISO7816.OFFSET_CDATA] + buffer[ISO7816.OFFSET_LC]));
    }
    
}