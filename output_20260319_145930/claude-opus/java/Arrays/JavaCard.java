import javacard.framework.*;

/*@
predicate MyApplet_someByteArray(byte[] arr;) =
    arr != null &*& array_slice(arr, 0, arr.length, _);

predicate MyApplet(MyApplet applet;) =
    applet != null;
@*/

public final class MyApplet extends Applet {
    static byte someByteArray[];
    
    //@ requires true;
    //@ ensures result != null &*& MyApplet(result);
    public MyApplet()
    {
        //@ close MyApplet(this);
    }
    
    public static void install(byte[] array, short offset, byte length)
        //@ requires array != null &*& array_slice(array, 0, array.length, _) &*& offset >= 0 &*& offset + 4 < array.length &*& array.length > offset + 1;
        //@ ensures true;
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
            //@ close MyApplet_someByteArray(someByteArray);
            
            theApplet.register();
            return;
        } else
            ISOException.throwIt(ISO7816.SW_FUNC_NOT_SUPPORTED); 
    }
    
    public boolean select()
        //@ requires MyApplet_someByteArray(?arr) &*& arr.length > 17;
        //@ ensures MyApplet_someByteArray(arr);
    {
        //@ open MyApplet_someByteArray(arr);
        JCSystem.beginTransaction();
        
        someByteArray[17] = 42; 
        
        JCSystem.commitTransaction();
        //@ close MyApplet_someByteArray(someByteArray);
        return true;
    }
    
    public void process(APDU apdu)
        //@ requires apdu != null;
        //@ ensures true;
    {
        byte[] buffer = apdu.getBuffer();
        //@ assume buffer != null &*& array_slice(buffer, 0, buffer.length, _) &*& buffer.length > ISO7816.OFFSET_INS;
        
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