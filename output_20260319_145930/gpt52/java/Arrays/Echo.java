package echo;

import javacard.framework.*;

/*@

predicate Echo_pred(Echo e) = e != null &*& e.Applet_pred();

@*/

public class Echo extends Applet {
    
    
    
    
    private static final byte Echo_CLA = (byte) 0xB0;
    private static final byte Echo_INS = (byte) 0x01;
    
    
    //@ requires bArray != null ? bArray.length >= 0 : true;
    //@ ensures true;
    public static void install(byte[] bArray, short bOffset, byte bLength) 
    
    
    {
        Echo echo = new Echo();
        //@ close Echo_pred(echo);
        //@ open Echo_pred(echo);
        //@ close echo.Applet_pred();
        echo.register();
    }
    
    //@ requires Echo_pred(this) &*& apdu != null;
    //@ ensures Echo_pred(this);
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
    
    //@ requires Echo_pred(this) &*& apdu != null;
    //@ ensures Echo_pred(this);
    private void echo(APDU apdu)
    
    
    {
        byte[] buffer = apdu.getBuffer();
        
        apdu.setOutgoing();
        
        apdu.setOutgoingLength(buffer[ISO7816.OFFSET_LC]);
        
        apdu.sendBytes((short)buffer[ISO7816.OFFSET_CDATA], (short)(buffer[ISO7816.OFFSET_CDATA] + buffer[ISO7816.OFFSET_LC]));
    }
    
}