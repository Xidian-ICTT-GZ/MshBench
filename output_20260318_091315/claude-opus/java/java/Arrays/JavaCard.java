import javacard.framework.*;

public final class MyApplet extends Applet {
    static byte someByteArray[];
    
    //@ predicate someByteArray_pred() = someByteArray != null &*& someByteArray.length > 17 &*& array_slice(someByteArray, 0, someByteArray.length);
    //@ predicate MyApplet_instance(MyApplet a) = a |-> _;
    
    //@ requires array != null &*& offset >= 0 &*& offset + length <= array.length &*& length >= 3 &*& length <= 127;
    //@ ensures  true; // no ownership transferred, no heap changes visible to caller
    public static void install(byte[] array, short offset, byte length)
        
    {
        //@ open array_slice(array, offset, length);
        MyApplet theApplet = new MyApplet();
        
        byte iLen = array[offset]; 
        offset = (short)(offset + iLen + 1);
        
        byte cLen = array[offset]; 
        offset = (short)(offset + cLen + 1);
        
        byte aLen = array[offset]; 
        
        
        byte bLen = array[(short)(offset + 1)];
        
        if (bLen != 0) {
            someByteArray = new byte[bLen];
            //@ close someByteArray_pred();
            theApplet.register();
            return;
        } else
            ISOException.throwIt(ISO7816.SW_FUNC_NOT_SUPPORTED); 
    }
    
    //@ requires someByteArray_pred() &*& JCSystem_transaction();
    //@ ensures someByteArray_pred() &*& JCSystem_transaction();
    public boolean select()
        
    {
        JCSystem.beginTransaction();
        //@ open someByteArray_pred();
        someByteArray[17] = 42; 
        //@ close someByteArray_pred();
        JCSystem.commitTransaction();
        return true;
    }
    
    //@ requires apdu != null &*& apdu.buffer(bytes) &*& bytes == array_slice(_, 0, _);
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