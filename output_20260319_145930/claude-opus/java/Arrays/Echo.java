package echo;

import javacard.framework.*;

/*@
predicate Echo_pred(Echo e;) = e != null;

predicate APDU_pred(APDU apdu; byte[] buffer) =
    apdu != null &*& apdu.buffer |-> buffer &*& buffer != null &*& array_slice(buffer, 0, buffer.length, _);
@*/

public class Echo extends Applet {
    
    
    
    
    private static final byte Echo_CLA = (byte) 0xB0;
    private static final byte Echo_INS = (byte) 0x01;
    
    
    public static void install(byte[] bArray, short bOffset, byte bLength) 
    //@ requires true;
    //@ ensures true;
    {
        Echo echo = new Echo();
        //@ close Echo_pred(echo);
        echo.register();
    }
    
    public void process(APDU apdu) 
    //@ requires APDU_pred(apdu, ?buffer) &*& Echo_pred(this);
    //@ ensures APDU_pred(apdu, buffer) &*& Echo_pred(this);
    {
        //@ open APDU_pred(apdu, buffer);
        byte[] buffer = apdu.getBuffer();
        
        if(selectingApplet()) {
            //@ close APDU_pred(apdu, buffer);
            return;
        }
        
        if(buffer[ISO7816.OFFSET_CLA] != Echo_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
        if(buffer[ISO7816.OFFSET_INS] != Echo_INS)
            ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        else {
            //@ close APDU_pred(apdu, buffer);
            echo(apdu);
        }
    }
    
    private void echo(APDU apdu)
    //@ requires APDU_pred(apdu, ?buffer) &*& Echo_pred(this);
    //@ ensures APDU_pred(apdu, buffer) &*& Echo_pred(this);
    {
        //@ open APDU_pred(apdu, buffer);
        byte[] buffer = apdu.getBuffer();
        
        apdu.setOutgoing();
        
        apdu.setOutgoingLength(buffer[ISO7816.OFFSET_LC]);
        
        apdu.sendBytes((short)buffer[ISO7816.OFFSET_CDATA], (short)(buffer[ISO7816.OFFSET_CDATA] + buffer[ISO7816.OFFSET_LC]));
        //@ close APDU_pred(apdu, buffer);
    }
    
}