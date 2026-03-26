package Store;

import javacard.framework.*;

public final class Store extends Applet {
    
    private static final byte Store_CLA = (byte) 0xB0;
    
    private static final byte SET = (byte) 0x10;
    private static final byte GET = (byte) 0x20;
    
    /*@ predicate value_array(byte[] a, int length) = a |-> ?arr &*& arr.length == length; @*/
    
    private static byte value[];
    
    //@ requires true;
    //@ ensures value_array(value, 5);
    public static void install(byte[] bArray, short bOffset, byte bLength)
    {
        Store store = new Store();
        store.register();
    }
    
    //@ requires true;
    //@ ensures value_array(value, 5);
    protected Store()
    {
        value = new byte[5];
    }
    
    //@ requires apdu != null &*& apdu.getBuffer() |-> ?buf &*& buf.length >= ISO7816.OFFSET_INS+1 &*& buf.length >= ISO7816.OFFSET_LC+1;
    //@ requires value_array(value, 5);
    //@ ensures value_array(value, 5);
    public void process(APDU apdu)
    {
        byte[] abuffer = apdu.getBuffer();
        
        if(selectingApplet())
            return;
        
        //@ assume abuffer != null;
        //@ assume abuffer.length > ISO7816.OFFSET_CLA;
        if(abuffer[ISO7816.OFFSET_CLA] != Store_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
        
        switch(abuffer[ISO7816.OFFSET_INS]) {
            case GET: get(apdu); return;
            case SET: set(apdu); return;
            default: ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        }
    }
    
    //@ requires apdu != null &*& apdu.getBuffer() |-> ?buf &*& buf.length >= ISO7816.OFFSET_LC + 1;
    //@ requires buf[ISO7816.OFFSET_LC] >= 0 &*& ((buf[ISO7816.OFFSET_LC] & 0xff) <= 5);
    //@ requires value_array(value, 5);
    //@ ensures value_array(value, 5);
    private final void set(APDU apdu)
    {
        byte[] abuffer = apdu.getBuffer();
        
        if((abuffer[ISO7816.OFFSET_LC] & 0xff) > 5)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        JCSystem.beginTransaction();
        
        Util.arrayCopy(abuffer, (short)ISO7816.OFFSET_CDATA, value, (short)0, (short)(abuffer[ISO7816.OFFSET_LC] & 0xff));
        
        JCSystem.commitTransaction();
    }
    
    //@ requires apdu != null &*& apdu.getBuffer() |-> ?buf &*& buf.length >= ISO7816.OFFSET_LC + 1;
    //@ requires value_array(value, 5);
    //@ requires buf[ISO7816.OFFSET_LC] >= 0;
    //@ ensures value_array(value, 5);
    private void get(APDU apdu)
    {
        byte[] abuffer = apdu.getBuffer();
        
        apdu.setOutgoing();
        apdu.setOutgoingLength(abuffer[ISO7816.OFFSET_LC]);
        
        apdu.sendBytesLong(value, (short)0, (short)value.length);
    }
    
}