package Store;

import javacard.framework.*;

public final class Store extends Applet {
    
    
    private static final byte Store_CLA = (byte) 0xB0;
    
    private static final byte SET = (byte) 0x10;
    private static final byte GET = (byte) 0x20;
    
    
    private static byte value[];
    
    //@ predicate Store() = value != null &*& array_slice(value, 0, 5, _);
    //@ predicate Store_ctor() = true;
    
    

    
    public static void install(byte[] bArray, short bOffset, byte bLength)
        //@ requires true;
        //@ ensures true;
    {
        
        Store store = new Store();
        store.register();
    }
    
    protected Store()
        //@ requires true;
        //@ ensures Store();
    {
        value = new byte[5];
        //@ close Store();
    }
    
    public void process(APDU apdu)
        //@ requires [?f]APDU(apdu) &*& Store();
        //@ ensures [f]APDU(apdu) &*& Store();
    {
        byte[] abuffer = apdu.getBuffer();
        //@ assert abuffer != null;
        
        if(selectingApplet())
            return;
        
        if(abuffer[ISO7816.OFFSET_CLA] != Store_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
        
        switch(abuffer[ISO7816.OFFSET_INS]) {
            case GET: 
                //@ open Store();
                get(apdu); 
                //@ close Store();
                return;
            case SET: 
                //@ open Store();
                set(apdu); 
                //@ close Store();
                return;
            default: ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        }
    }
    
    private final void set(APDU apdu)
        //@ requires [?f]APDU(apdu) &*& array_slice(value, 0, 5, _);
        //@ ensures [f]APDU(apdu) &*& array_slice(value, 0, 5, _);
    {
        byte[] abuffer = apdu.getBuffer();
        //@ assert abuffer != null;
        
        
        if((abuffer[ISO7816.OFFSET_LC] & 0xff) > 5)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        JCSystem.beginTransaction();
        
        //@ assert 0 <= (abuffer[ISO7816.OFFSET_LC] & 0xff) &*& (abuffer[ISO7816.OFFSET_LC] & 0xff) <= 5;
        Util.arrayCopy(abuffer, (short)ISO7816.OFFSET_CDATA, value, (short)0, (short)(abuffer[ISO7816.OFFSET_LC] & 0xff));
        
        JCSystem.commitTransaction();
    }
    
    private void get(APDU apdu)
        //@ requires [?f]APDU(apdu) &*& array_slice(value, 0, 5, _);
        //@ ensures [f]APDU(apdu) &*& array_slice(value, 0, 5, _);
    {
        byte[] abuffer = apdu.getBuffer();
        //@ assert abuffer != null;
        
        apdu.setOutgoing();
        apdu.setOutgoingLength(abuffer[ISO7816.OFFSET_LC]);
        
        
        
        apdu.sendBytesLong(value, (short)0, (short)value.length);
        
    }
    
}