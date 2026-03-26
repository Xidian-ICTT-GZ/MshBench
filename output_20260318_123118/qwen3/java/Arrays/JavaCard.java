/*@ predicate someByteArray_initialized(byte[] arr; byte len) =
    arr != null &*&
    array_slice(arr, 0, len, _);
@*/

import javacard.framework.*;

public final class MyApplet extends Applet {
    static byte someByteArray[];
    
    /*@
    predicate_class MyApplet() = true;
    @*/
    
    //@ requires array != null &*& array_slice(array, offset, (short)(length + offset), _) &*& length >= 3 &*& offset >= 0 &*& (short)(offset + length) <= array.length;
    //@ ensures true;
    public static void install(byte[] array, short offset, byte length)
    {
        MyApplet theApplet = new MyApplet();
        
        byte iLen = array[offset]; 
        offset = (short)(offset + iLen + 1);
        
        byte cLen = array[offset]; 
        offset = (short)(offset + cLen + 1);
        
        byte aLen = array[offset]; 
        
        byte bLen = array[(short)(offset + 1)];
        
        if (bLen != 0) {
            someByteArray = new byte[bLen];
            /*@ close someByteArray_initialized(someByteArray, bLen); @*/
            
            theApplet.register();
            return;
        } else
            ISOException.throwIt(ISO7816.SW_FUNC_NOT_SUPPORTED); 
    }
    
    //@ requires someByteArray != null &*& array_slice(someByteArray, 0, someByteArray.length, _) &*& someByteArray.length > 17;
    //@ ensures result == true;
    public boolean select()
    {
        JCSystem.beginTransaction();
        
        someByteArray[17] = 42; 
        
        JCSystem.commitTransaction();
        return true;
    }
    
    //@ requires apdu != null &*& APDU(apdu, ?buffer, ?buffer_length) &*& buffer != null &*& array_slice(buffer, 0, buffer_length, _);
    //@ ensures true;
    public void process(APDU apdu)
    {
        byte[] buffer = apdu.getBuffer();
        
        if (buffer[ISO7816.OFFSET_CLA] == (byte)0) {
            switch (buffer[ISO7816.OFFSET_INS]) {
                case ISO7816.INS_SELECT:
                    short length = apdu.setOutgoing();
                    byte[] replyData = new byte[10];
                    
                    if (length < 20) ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
                    apdu.setOutgoingLength((short)replyData.length);
                    apdu.sendBytesLong(replyData, (short)0, (short)replyData.length);
                    break;
                
            }
        }
    }
}