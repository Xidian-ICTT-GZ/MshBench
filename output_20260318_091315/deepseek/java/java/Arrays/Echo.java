package echo;

import javacard.framework.*;

//@ predicate EchoPred() = true;

public class Echo extends Applet {
    
    
    
    
    private static final byte Echo_CLA = (byte) 0xB0;
    private static final byte Echo_INS = (byte) 0x01;
    
    
    public static void install(byte[] bArray, short bOffset, byte bLength) 
    //@ requires true;
    //@ ensures true;
    {
        Echo echo = new Echo();
        
        echo.register();
    }
    
    public void process(APDU apdu) 
    //@ requires APDU(apdu, ?buffer) &*& buffer != null &*& buffer.length > 0 &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
        
        byte[] buffer = apdu.getBuffer();
        
        if(selectingApplet())
            return;
        
        if(buffer[ISO7816.OFFSET_CLA] != Echo_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
        if(buffer[ISO7816.OFFSET_INS] != Echo_INS)
            ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        else
            echo(apdu);
    }
    
    private void echo(APDU apdu)
    //@ requires APDU(apdu, ?buffer) &*& buffer != null &*& buffer.length > 0 &*& array_slice(buffer, 0, buffer.length, ?contents) &*& 0 <= ISO7816.OFFSET_LC &*& ISO7816.OFFSET_LC < buffer.length &*& 0 <= ISO7816.OFFSET_CDATA &*& ISO7816.OFFSET_CDATA < buffer.length &*& 0 <= buffer[ISO7816.OFFSET_LC] &*& buffer[ISO7816.OFFSET_LC] <= buffer.length - ISO7816.OFFSET_CDATA;
    //@ ensures APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, contents);
    {
        byte[] buffer = apdu.getBuffer();
        
        apdu.setOutgoing();
        
        apdu.setOutgoingLength(buffer[ISO7816.OFFSET_LC]);
        
        apdu.sendBytes((short)buffer[ISO7816.OFFSET_CDATA], (short)(buffer[ISO7816.OFFSET_CDATA] + buffer[ISO7816.OFFSET_LC]));
    }
    
}