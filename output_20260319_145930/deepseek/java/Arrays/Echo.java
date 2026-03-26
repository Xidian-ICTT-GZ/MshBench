package echo;

import javacard.framework.*;

public class Echo extends Applet {
    
    
    
    
    private static final byte Echo_CLA = (byte) 0xB0;
    private static final byte Echo_INS = (byte) 0x01;
    
    //@ predicate EchoPred() = true;
    
    //@ requires true;
    //@ ensures EchoPred();
    public Echo() 
    {
        //@ close EchoPred();
    }
    
    
    //@ requires true;
    //@ ensures true;
    public static void install(byte[] bArray, short bOffset, byte bLength) 
    
    
    {
        Echo echo = new Echo();
        
        echo.register();
    }
    
    //@ requires apdu != null &*& apdu.APDUPred();
    //@ ensures apdu.APDUPred();
    public void process(APDU apdu) 
    
    
    {
        //@ open EchoPred();
        //@ open apdu.APDUPred();
        byte[] buffer = apdu.getBuffer();
        //@ close apdu.APDUPred();
        
        if(selectingApplet()) {
            //@ close EchoPred();
            return;
        }
        
        if(buffer[ISO7816.OFFSET_CLA] != Echo_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
        if(buffer[ISO7816.OFFSET_INS] != Echo_INS)
            ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        else
            echo(apdu);
        //@ close EchoPred();
    }
    
    //@ requires apdu != null &*& apdu.APDUPred();
    //@ ensures apdu.APDUPred();
    private void echo(APDU apdu)
    
    
    {
        //@ open apdu.APDUPred();
        byte[] buffer = apdu.getBuffer();
        
        apdu.setOutgoing();
        
        apdu.setOutgoingLength(buffer[ISO7816.OFFSET_LC]);
        
        apdu.sendBytes((short)buffer[ISO7816.OFFSET_CDATA], (short)(buffer[ISO7816.OFFSET_CDATA] + buffer[ISO7816.OFFSET_LC]));
        //@ close apdu.APDUPred();
    }
    
}