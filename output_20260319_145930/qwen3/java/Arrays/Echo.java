package echo;

import javacard.framework.*;

/*@ 
predicate Echo_applet(Echo e;) = true;
@*/

public class Echo extends Applet {
    
    private static final byte Echo_CLA = (byte) 0xB0;
    private static final byte Echo_INS = (byte) 0x01;
    
    //@ requires true;
    //@ ensures true;
    public static void install(byte[] bArray, short bOffset, byte bLength) 
    {
        Echo echo = new Echo();
        //@ close Echo_applet(echo);
        echo.register();
    }
    
    //@ requires [?f]Echo_applet(this);
    //@ ensures [f]Echo_applet(this);
    public void process(APDU apdu) 
    {
        //@ open Echo_applet(this);
        byte[] buffer = apdu.getBuffer();
        
        if(selectingApplet()) {
            //@ close Echo_applet(this);
            return;
        }
        
        if(buffer[ISO7816.OFFSET_CLA] != Echo_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
        if(buffer[ISO7816.OFFSET_INS] != Echo_INS)
            ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        else
            echo(apdu);
        //@ close Echo_applet(this);
    }
    
    //@ requires [?f]Echo_applet(this);
    //@ ensures [f]Echo_applet(this);
    private void echo(APDU apdu)
    {
        //@ open Echo_applet(this);
        byte[] buffer = apdu.getBuffer();
        
        apdu.setOutgoing();
        
        apdu.setOutgoingLength(buffer[ISO7816.OFFSET_LC]);
        
        apdu.sendBytes((short)buffer[ISO7816.OFFSET_CDATA], (short)(buffer[ISO7816.OFFSET_CDATA] + buffer[ISO7816.OFFSET_LC]));
        //@ close Echo_applet(this);
    }
    
}