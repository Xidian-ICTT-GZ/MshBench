import javacard.framework.*;

public final class MyApplet extends Applet {
    static byte someByteArray[];
    
    //@ predicate valid() = someByteArray |-> ?a &*& (a == null ? true : array_slice(a, 0, a.length, _));
    
    public static void install(byte[] array, short offset, byte length)
    {
        //@ close true;
        MyApplet theApplet = new MyApplet();
        //@ close theApplet.valid();
        
        byte iLen = array[offset]; 
        offset = (short)(offset + iLen + 1);
        
        byte cLen = array[offset]; 
        offset = (short)(offset + cLen + 1);
        
        byte aLen = array[offset]; 
        
        byte bLen = array[(short)(offset + 1)];
        
        if (bLen != 0) {
            someByteArray = new byte[bLen];
            //@ close theApplet.valid();
            
            theApplet.register();
            return;
        } else
            ISOException.throwIt(ISO7816.SW_FUNC_NOT_SUPPORTED); 
    }
    
    public boolean select()
    {
        //@ open valid();
        JCSystem.beginTransaction();
        
        someByteArray[17] = 42; 
        
        JCSystem.commitTransaction();
        //@ close valid();
        return true;
    }
    
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