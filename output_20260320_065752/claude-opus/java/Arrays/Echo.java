package echo;

import javacard.framework.*;

/*@
predicate Echo_inv(Echo this) = true;
@*/

public class Echo extends Applet {
    
    private static final byte Echo_CLA = (byte) 0xB0;
    private static final byte Echo_INS = (byte) 0x01;
    
    //@ requires true;
    //@ ensures true;
    public static void install(byte[] bArray, short bOffset, byte bLength) 
    {
        Echo echo = new Echo();
        echo.register();
    }
    
    //@ requires this.Echo_inv(this) &*& apdu != null;
    //@ ensures this.Echo_inv(this);
    public void process(APDU apdu) 
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
    
    //@ requires this.Echo_inv(this) &*& apdu != null;
    //@ ensures this.Echo_inv(this);
    private void echo(APDU apdu)
    {
        byte[] buffer = apdu.getBuffer();
        
        apdu.setOutgoing();
        
        apdu.setOutgoingLength(buffer[ISO7816.OFFSET_LC]);
        
        apdu.sendBytes((short)buffer[ISO7816.OFFSET_CDATA], (short)(buffer[ISO7816.OFFSET_CDATA] + buffer[ISO7816.OFFSET_LC]));
    }
}