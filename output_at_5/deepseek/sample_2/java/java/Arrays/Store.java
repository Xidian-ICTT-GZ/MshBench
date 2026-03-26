package Store;

import javacard.framework.*;

public final class Store extends Applet {
    
    
    private static final byte Store_CLA = (byte) 0xB0;
    
    private static final byte SET = (byte) 0x10;
    private static final byte GET = (byte) 0x20;
    
    
    private static byte value[];
    
    

    
    public static void install(byte[] bArray, short bOffset, byte bLength)
        //@ requires true;
        //@ ensures true;
    {
        
        Store store = new Store();
        store.register();
    }
    
    protected Store()
        //@ requires true;
        //@ ensures StorePred(value);
    {
        value = new byte[5];
        //@ close StorePred(value);
    }
    
    public void process(APDU apdu)
        //@ requires StorePred(value);
        //@ ensures StorePred(value);
    {
        byte[] abuffer = apdu.getBuffer();
        
        if(selectingApplet())
            //@ close StorePred(value);
            return;
        
        if(abuffer[ISO7816.OFFSET_CLA] != Store_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
        
        switch(abuffer[ISO7816.OFFSET_INS]) {
            case GET: 
                get(apdu); 
                //@ close StorePred(value);
                return;
            case SET: 
                set(apdu); 
                //@ close StorePred(value);
                return;
            default: 
                ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        }
    }
    
    private final void set(APDU apdu)
        //@ requires StorePred(value);
        //@ ensures StorePred(value);
    {
        byte[] abuffer = apdu.getBuffer();
        
        
        if((abuffer[ISO7816.OFFSET_LC] & 0xff) > 5)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        JCSystem.beginTransaction();
        
        //@ open StorePred(value);
        Util.arrayCopy(abuffer, (short)ISO7816.OFFSET_CDATA, value, (short)0, (short)(abuffer[ISO7816.OFFSET_LC] & 0xff));
        //@ close StorePred(value);
        JCSystem.commitTransaction();
    }
    
    private void get(APDU apdu)
        //@ requires StorePred(value);
        //@ ensures StorePred(value);
    {
        byte[] abuffer = apdu.getBuffer();
        
        apdu.setOutgoing();
        apdu.setOutgoingLength(abuffer[ISO7816.OFFSET_LC]);
        
        
        //@ open StorePred(value);
        apdu.sendBytesLong(value, (short)0, (short)value.length);
        //@ close StorePred(value);
    }
    
    /*@
    predicate StorePred(byte[] v) = 
        v == value &*& v != null &*& v.length == 5 &*& array_slice(v, 0, 5, _);
    @*/
}