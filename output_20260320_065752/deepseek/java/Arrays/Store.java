package Store;

import javacard.framework.*;

public final class Store extends Applet {
    
    
    private static final byte Store_CLA = (byte) 0xB0;
    
    private static final byte SET = (byte) 0x10;
    private static final byte GET = (byte) 0x20;
    
    
    private static byte value[];
    
    

/*@
predicate StoreInv(Store s;) = s.value |-> ?v &*& v != null &*& array_slice(v, 0, v.length, _);
@*/
    
    public static void install(byte[] bArray, short bOffset, byte bLength)
        //@ requires true;
        //@ ensures true;
    {
        
        Store store = new Store();
        store.register();
    }
    
    protected Store()
        //@ requires true;
        //@ ensures StoreInv(this);
    {
        value = new byte[5];
        //@ close StoreInv(this);
    }
    
    public void process(APDU apdu)
        //@ requires StoreInv(this);
        //@ ensures StoreInv(this);
    {
        byte[] abuffer = apdu.getBuffer();
        
        if(selectingApplet())
            //@ close StoreInv(this);
            return;
        
        if(abuffer[ISO7816.OFFSET_CLA] != Store_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
        
        switch(abuffer[ISO7816.OFFSET_INS]) {
            case GET: 
                //@ open StoreInv(this);
                get(apdu); 
                //@ close StoreInv(this);
                return;
            case SET: 
                //@ open StoreInv(this);
                set(apdu); 
                //@ close StoreInv(this);
                return;
            default: ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        }
    }
    
    private final void set(APDU apdu)
        //@ requires StoreInv(this);
        //@ ensures StoreInv(this);
    {
        byte[] abuffer = apdu.getBuffer();
        
        
        if((abuffer[ISO7816.OFFSET_LC] & 0xff) > 5)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        JCSystem.beginTransaction();
        
        //@ open StoreInv(this);
        Util.arrayCopy(abuffer, (short)ISO7816.OFFSET_CDATA, value, (short)0, (short)(abuffer[ISO7816.OFFSET_LC] & 0xff));
        //@ close StoreInv(this);
        JCSystem.commitTransaction();
    }
    
    private void get(APDU apdu)
        //@ requires StoreInv(this);
        //@ ensures StoreInv(this);
    {
        byte[] abuffer = apdu.getBuffer();
        
        apdu.setOutgoing();
        apdu.setOutgoingLength(abuffer[ISO7816.OFFSET_LC]);
        
        //@ open StoreInv(this);
        apdu.sendBytesLong(value, (short)0, (short)value.length);
        //@ close StoreInv(this);
        
    }
    
}