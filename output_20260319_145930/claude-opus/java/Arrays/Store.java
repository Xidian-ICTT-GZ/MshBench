package Store;

import javacard.framework.*;

public final class Store extends Applet {
    
    
    private static final byte Store_CLA = (byte) 0xB0;
    
    private static final byte SET = (byte) 0x10;
    private static final byte GET = (byte) 0x20;
    
    
    private static byte value[];
    
    

    /*@
    predicate valid() =
        value |-> ?v &*& v != null &*& array_slice(v, 0, v.length, _) &*& v.length == 5;
    @*/

    
    public static void install(byte[] bArray, short bOffset, byte bLength)
        //@ requires system();
        //@ ensures true;
    {
        
        Store store = new Store();
        store.register();
    }
    
    protected Store()
        //@ requires system();
        //@ ensures valid();
    {
        value = new byte[5];
        //@ close valid();
    }
    
    public void process(APDU apdu)
        //@ requires valid() &*& apdu != null &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _) &*& buffer.length >= 5;
        //@ ensures valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
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
        //@ requires valid() &*& apdu != null &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _) &*& buffer.length >= 5;
        //@ ensures valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
        byte[] abuffer = apdu.getBuffer();
        
        
        if((abuffer[ISO7816.OFFSET_LC] & 0xff) > 5)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        JCSystem.beginTransaction();
        
        //@ open valid();
        
        Util.arrayCopy(abuffer, (short)ISO7816.OFFSET_CDATA, value, (short)0, (short)(abuffer[ISO7816.OFFSET_LC] & 0xff));
        
        //@ close valid();
        JCSystem.commitTransaction();
    }
    
    private void get(APDU apdu)
        //@ requires valid() &*& apdu != null &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _) &*& buffer.length >= 5;
        //@ ensures valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
        byte[] abuffer = apdu.getBuffer();
        
        apdu.setOutgoing();
        apdu.setOutgoingLength(abuffer[ISO7816.OFFSET_LC]);
        
        //@ open valid();
        
        apdu.sendBytesLong(value, (short)0, (short)value.length);
        
        //@ close valid();
    }
    
}