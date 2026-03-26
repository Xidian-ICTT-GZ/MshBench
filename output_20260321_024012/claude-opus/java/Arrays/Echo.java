package echo;

import javacard.framework.*;

public class Echo extends Applet {
    
    /*@
    predicate object_inv(Echo this) = true;
    @*/

    
    
    private static final byte Echo_CLA = (byte) 0xB0;
    private static final byte Echo_INS = (byte) 0x01;
    
    
    //@ public normal_behavior
    //@ requires true;
    //@ ensures object_inv(this);
    public static void install(byte[] bArray, short bOffset, byte bLength) 
    
    
    {
        Echo echo = new Echo();
        //@ close object_inv(echo);
        echo.register();
    }
    
    //@ public normal_behavior
    //@ requires object_inv(this);
    //@ ensures object_inv(this);
    public void process(APDU apdu) 
    
    
    {
        //@ open object_inv(this);
        byte[] buffer = apdu.getBuffer();
        
        if(selectingApplet())
        {
            //@ close object_inv(this);
            return;
        }
        
        if(buffer[ISO7816.OFFSET_CLA] != Echo_CLA)
        {
            //@ close object_inv(this);
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
        }
        if(buffer[ISO7816.OFFSET_INS] != Echo_INS)
        {
            //@ close object_inv(this);
            ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        }
        else
        {
            echo(apdu);
        }
        //@ close object_inv(this);
    }
    
    //@ private normal_behavior
    //@ requires object_inv(this);
    //@ requires apdu != null && apdu.getBuffer() != null;
    //@ ensures object_inv(this);
    private void echo(APDU apdu)
    
    
    {
        //@ open object_inv(this);
        byte[] buffer = apdu.getBuffer();
        
        apdu.setOutgoing();
        
        apdu.setOutgoingLength(buffer[ISO7816.OFFSET_LC]);
        
        apdu.sendBytes((short)buffer[ISO7816.OFFSET_CDATA], (short)(buffer[ISO7816.OFFSET_CDATA] + buffer[ISO7816.OFFSET_LC]));
        //@ close object_inv(this);
    }
    
}