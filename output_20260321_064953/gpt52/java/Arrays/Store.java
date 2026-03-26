package Store;

import javacard.framework.*;

public final class Store extends Applet {
    
    /*@
    predicate store_state() =
        value != null &*& value.length == 5;
    @*/
    
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
    //@ ensures store_state();
    protected Store()
        
        
    {
        value = new byte[5];
        //@ close store_state();
        
    }
    
    //@ requires store_state();
    //@ ensures store_state();
    public void process(APDU apdu)
        
        
    {
        //@ open store_state();
        byte[] abuffer = apdu.getBuffer();
        
        if(selectingApplet()) {
            //@ close store_state();
            return;
        }
        
        if(abuffer[ISO7816.OFFSET_CLA] != Store_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
        
        switch(abuffer[ISO7816.OFFSET_INS]) {
            case GET: 
                //@ close store_state();
                get(apdu); 
                return;
            case SET: 
                //@ close store_state();
                set(apdu); 
                return;
            default: ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        }
        //@ close store_state();
    }
    
    //@ requires store_state();
    //@ ensures store_state();
    private final void set(APDU apdu)
        
        
    {
        //@ open store_state();
        byte[] abuffer = apdu.getBuffer();
        
        
        if((abuffer[ISO7816.OFFSET_LC] & 0xff) > 5)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        JCSystem.beginTransaction();
        
        
        Util.arrayCopy(abuffer, (short)ISO7816.OFFSET_CDATA, value, (short)0, (short)(abuffer[ISO7816.OFFSET_LC] & 0xff));
        
        JCSystem.commitTransaction();
        //@ close store_state();
    }
    
    //@ requires store_state();
    //@ ensures store_state();
    private void get(APDU apdu)
    
    
    {
        //@ open store_state();
        byte[] abuffer = apdu.getBuffer();
        
        apdu.setOutgoing();
        apdu.setOutgoingLength(abuffer[ISO7816.OFFSET_LC]);
        
        
        
        apdu.sendBytesLong(value, (short)0, (short)value.length);
        
        //@ close store_state();
    }
    
}