import javacard.framework.*;

public final class MyApplet extends Applet {
    static byte someByteArray[];
    
    public static void install(byte[] array, short offset, byte length)
    //@ requires array != null &*& array.length >= 0;
    //@ ensures true;
    {
        MyApplet theApplet = new MyApplet();
        
        //@ assume 0 <= offset;
        //@ assume offset < array.length;
        byte iLen = array[offset]; 
        offset = (short)(offset + iLen + 1);
        
        //@ assume 0 <= offset;
        //@ assume offset < array.length;
        byte cLen = array[offset]; 
        offset = (short)(offset + cLen + 1);
        
        //@ assume 0 <= offset;
        //@ assume offset < array.length;
        byte aLen = array[offset]; 
        
        
        //@ assume 0 <= (short)(offset + 1);
        //@ assume (short)(offset + 1) < array.length;
        byte bLen = array[(short)(offset + 1)];
        
        if (bLen != 0) {
            //@ assume 0 <= bLen;
            someByteArray = new byte[bLen];
            
            theApplet.register();
            return;
        } else
            ISOException.throwIt(ISO7816.SW_FUNC_NOT_SUPPORTED); 
    }
    
    public boolean select()
    //@ requires true;
    //@ ensures true;
    {
        
        JCSystem.beginTransaction();
        
        //@ assume someByteArray != null;
        //@ assume 18 <= someByteArray.length;
        someByteArray[17] = 42; 
        
        JCSystem.commitTransaction();
        return true;
    }
    
    public void process(APDU apdu)
    //@ requires apdu != null;
    //@ ensures true;
    {
        byte[] buffer = apdu.getBuffer();
        
        //@ assume buffer != null;
        //@ assume 0 <= ISO7816.OFFSET_CLA && ISO7816.OFFSET_CLA < buffer.length;
        if (buffer[ISO7816.OFFSET_CLA] == (byte)0) {
            //@ assume 0 <= ISO7816.OFFSET_INS && ISO7816.OFFSET_INS < buffer.length;
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