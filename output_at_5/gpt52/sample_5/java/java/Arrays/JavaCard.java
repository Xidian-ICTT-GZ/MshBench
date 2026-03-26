import javacard.framework.*;

/*@
predicate byte_array(byte[] a; int n) =
    a != null &*& array_slice(a, 0, n, _);

predicate static_state() =
    someByteArray == null ? emp : byte_array(someByteArray, _);

@*/

public final class MyApplet extends Applet {
    static byte someByteArray[];
    
    public static void install(byte[] array, short offset, byte length)
        //@ requires byte_array(array, ?n) &*& 0 <= offset &*& offset + 1 < n;
        /*@ ensures
              byte_array(array, n) &*& static_state();
        @*/
    {
        //@ open byte_array(array, n);
        
        MyApplet theApplet = new MyApplet();
        
        byte iLen = array[offset]; 
        offset = (short)(offset + iLen + 1);
        
        byte cLen = array[offset]; 
        offset = (short)(offset + cLen + 1);
        
        byte aLen = array[offset]; 
        
        
        byte bLen = array[(short)(offset + 1)];
        
        if (bLen != 0) {
            someByteArray = new byte[bLen];
            //@ close byte_array(someByteArray, bLen);
            //@ close static_state();
            //@ close byte_array(array, n);
            theApplet.register();
            return;
        } else {
            //@ close static_state();
            //@ close byte_array(array, n);
            ISOException.throwIt(ISO7816.SW_FUNC_NOT_SUPPORTED); 
        }
    }
    
    public boolean select()
        //@ requires byte_array(someByteArray, ?m) &*& 18 <= m;
        //@ ensures byte_array(someByteArray, m) &*& result == true;
    {
        //@ open byte_array(someByteArray, m);
        
        JCSystem.beginTransaction();
        
        someByteArray[17] = 42; 
        
        JCSystem.commitTransaction();
        //@ close byte_array(someByteArray, m);
        return true;
    }
    
    public void process(APDU apdu)
        //@ requires apdu != null;
        //@ ensures true;
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