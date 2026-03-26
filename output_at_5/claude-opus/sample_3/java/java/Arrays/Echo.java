package echo;

import javacard.framework.*;

public class Echo extends Applet {
    
    /*@
      predicate echo_inv() = true;
    @*/
    
    private static final byte Echo_CLA = (byte) 0xB0;
    private static final byte Echo_INS = (byte) 0x01;
    
    
    public static void install(byte[] bArray, short bOffset, byte bLength) 
    //@ requires true;
    //@ ensures true;
    {
        Echo echo = new Echo();
        //@ open echo_inv();
        echo.register();
        //@ close echo_inv();
    }
    
    public void process(APDU apdu) 
    //@ requires true;
    //@ ensures true;
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
    //@ requires true;
    //@ ensures true;
    {
        byte[] buffer = apdu.getBuffer();
        
        apdu.setOutgoing();
        
        apdu.setOutgoingLength(buffer[ISO7816.OFFSET_LC]);
        
        apdu.sendBytes((short)buffer[ISO7816.OFFSET_CDATA], (short)(buffer[ISO7816.OFFSET_CDATA] + buffer[ISO7816.OFFSET_LC]));
    }
    
}