package Store;

import javacard.framework.*;

/*@

predicate static_value(byte[] v) =
    v != null &*& v.length == 5 &*& chars(v, 0, 5, _);

@*/

public final class Store extends Applet {
    
    
    private static final byte Store_CLA = (byte) 0xB0;
    
    private static final byte SET = (byte) 0x10;
    private static final byte GET = (byte) 0x20;
    
    
    private static byte value[];
    
    

    
    //@ requires true;
    //@ ensures true;
    public static void install(byte[] bArray, short bOffset, byte bLength)
        
        
    {
        
        Store store = new Store();
        store.register();
    }
    
    //@ requires true;
    //@ ensures static_value(value);
    protected Store()
        
        
    {
        value = new byte[5];
        //@ close static_value(value);
        
    }
    
    //@ requires static_value(value);
    //@ ensures static_value(value);
    public void process(APDU apdu)
        
        
    {
        byte[] abuffer = apdu.getBuffer();
        
        if(selectingApplet())
            return;
        
        if(abuffer[ISO7816.OFFSET_CLA] != Store_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
        
        switch(abuffer[ISO7816.OFFSET_INS]) {
            case GET: get(apdu); return;
            case SET: set(apdu); return;
            default: ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        }
    }
    
    //@ requires static_value(value);
    //@ ensures static_value(value);
    private final void set(APDU apdu)
        
        
    {
        //@ open static_value(value);
        byte[] abuffer = apdu.getBuffer();
        
        
        if((abuffer[ISO7816.OFFSET_LC] & 0xff) > 5)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        JCSystem.beginTransaction();
        
        
        Util.arrayCopy(abuffer, (short)ISO7816.OFFSET_CDATA, value, (short)0, (short)(abuffer[ISO7816.OFFSET_LC] & 0xff));
        
        JCSystem.commitTransaction();
        //@ close static_value(value);
    }
    
    //@ requires static_value(value);
    //@ ensures static_value(value);
    private void get(APDU apdu)
    
    
    {
        //@ open static_value(value);
        byte[] abuffer = apdu.getBuffer();
        
        apdu.setOutgoing();
        apdu.setOutgoingLength(abuffer[ISO7816.OFFSET_LC]);
        
        
        
        apdu.sendBytesLong(value, (short)0, (short)value.length);
        
        //@ close static_value(value);
    }
    
}