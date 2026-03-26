package Store;

import javacard.framework.*;

public final class Store extends Applet {
    
    private static final byte Store_CLA = (byte) 0xB0;
    
    private static final byte SET = (byte) 0x10;
    private static final byte GET = (byte) 0x20;
    
    //@ predicate value_array_pred(byte[] a, int length) = a |-> ?data &*& length == 5 &*& array_slice(a, 0, length, ?contents) &*& length == contents.length;
    private static byte value[];
    
    public static void install(byte[] bArray, short bOffset, byte bLength)
        //@ requires bArray != null &*& bOffset >= 0 &*& bLength >= 0 &*& bOffset + bLength <= bArray.length;
        //@ ensures true;
    {
        Store store = new Store();
        store.register();
    }
    
    protected Store()
        //@ requires true;
        //@ ensures value != null &*& value.length == 5 &*& value_array_pred(value, 5);
    {
        value = new byte[5];
        //@ close value_array_pred(value, 5);
    }
    
    public void process(APDU apdu)
        //@ requires apdu != null &*& apdu.getBuffer() != null &*& array_slice(apdu.getBuffer(), 0, apdu.getBuffer().length, ?buf);
        //@ ensures true;
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
    
    private final void set(APDU apdu)
        //@ requires apdu != null &*& apdu.getBuffer() != null &*& array_slice(apdu.getBuffer(), 0, apdu.getBuffer().length, ?buf) &*& (buf[ISO7816.OFFSET_LC] & 0xff) <= 5;
        //@ ensures value_array_pred(value, 5);
    {
        byte[] abuffer = apdu.getBuffer();
        
        if((abuffer[ISO7816.OFFSET_LC] & 0xff) > 5)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        JCSystem.beginTransaction();
        //@ open value_array_pred(value, 5);
        Util.arrayCopy(abuffer, (short)ISO7816.OFFSET_CDATA, value, (short)0, (short)(abuffer[ISO7816.OFFSET_LC] & 0xff));
        //@ close value_array_pred(value, 5);
        JCSystem.commitTransaction();
    }
    
    private void get(APDU apdu)
        //@ requires apdu != null &*& apdu.getBuffer() != null &*& array_slice(apdu.getBuffer(), 0, apdu.getBuffer().length, ?buf) &*& value_array_pred(value, 5) &*& (0 <= buf[ISO7816.OFFSET_LC] &*& buf[ISO7816.OFFSET_LC] <= 5);
        //@ ensures true;
    {
        byte[] abuffer = apdu.getBuffer();
        
        apdu.setOutgoing();
        apdu.setOutgoingLength(abuffer[ISO7816.OFFSET_LC]);
        
        apdu.sendBytesLong(value, (short)0, (short)value.length);
    }
}