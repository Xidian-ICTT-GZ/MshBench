import javacard.framework.*;

/*@
predicate MyApplet_inv(MyApplet a) = true;
@*/

public final class MyApplet extends Applet {
    static byte someByteArray[];
    
    //@ requires true;
    //@ ensures true;
    public static void install(byte[] array, short offset, byte length)
    {
        MyApplet theApplet = new MyApplet();
        
        //@ open true;
        byte iLen = array[offset]; 
        offset = (short)(offset + iLen + 1);
        
        byte cLen = array[offset]; 
        offset = (short)(offset + cLen + 1);
        
        byte aLen = array[offset]; 
        
        byte bLen = array[(short)(offset + 1)];
        
        if (bLen != 0) {
            someByteArray = new byte[bLen];
            
            theApplet.register();
            //@ close true;
            return;
        } else {
            //@ close true;
            ISOException.throwIt(ISO7816.SW_FUNC_NOT_SUPPORTED); 
        }
    }
    
    //@ requires someByteArray != null &*& 0 <= 17 &*& 17 < someByteArray.length;
    //@ ensures result == true &*& someByteArray[17] == 42;
    public boolean select()
    {
        JCSystem.beginTransaction();
        
        someByteArray[17] = 42; 
        
        JCSystem.commitTransaction();
        return true;
    }
    
    //@ requires apdu != null &*& apdu.getBuffer() != null;
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