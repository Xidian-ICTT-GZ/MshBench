import javacard.framework.*;

public final class MyApplet extends Applet {
    static byte someByteArray[];
    
    /*@ predicate array_bytes(byte[] a; int length) = length == a.length &*& length >= 0; @*/

    /*@
    requires array != null &*& 0 <= offset &*& offset + length <= array.length &*& length > 0 &*&
             0 <= (array[offset]) &*& 0 <= (array[offset + (array[offset]) + 1]) &*&
             0 <= (array[offset + (array[offset]) + 1 + (array[offset + (array[offset]) + 1]) + 1]) &*&
             0 <= (array[(short)(offset + (array[offset + (array[offset]) + 1 + (array[offset + (array[offset]) + 1]) + 1]) + 1)]);
    ensures true;
    @*/
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
            /*@ if (bLen > 0) {
                  close array_bytes(new byte[bLen], bLen);
                }
            @*/
            someByteArray = new byte[bLen];
            
            theApplet.register();
            return;
        } else
            ISOException.throwIt(ISO7816.SW_FUNC_NOT_SUPPORTED); 
    }
    
    /*@
    requires someByteArray != null &*& 17 < someByteArray.length;
    ensures result == true &*& someByteArray[17] == 42;
    @*/
    public boolean select()
    {
        JCSystem.beginTransaction();
        
        someByteArray[17] = 42; 
        
        JCSystem.commitTransaction();
        return true;
    }
    
    /*@
    requires apdu != null &*& apdu.getBuffer() != null &*& apdu.getBuffer().length >= ISO7816.OFFSET_INS + 1;
    ensures true;
    @*/
    public void process(APDU apdu)
    {
        byte[] buffer = apdu.getBuffer();
        
        if (buffer[ISO7816.OFFSET_CLA] == (byte)0) {
            switch (buffer[ISO7816.OFFSET_INS]) {
                case ISO7816.INS_SELECT:
                    /*@
                    // length is at least 0; replyData length = 10
                    @*/
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