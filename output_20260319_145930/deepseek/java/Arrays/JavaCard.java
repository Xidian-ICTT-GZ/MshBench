import javacard.framework.*;

/*@
predicate MyApplet(MyApplet a;) = 
    a.someByteArray |-> ?arr &*& arr != null &*& array_slice(arr, 0, arr.length, _);
@*/

public final class MyApplet extends Applet {
    static byte someByteArray[];
    
    /*@
    predicate static_MyApplet() = 
        someByteArray |-> ?arr &*& arr != null ? array_slice(arr, 0, arr.length, _) : true;
    @*/
    
    /*@
    requires true;
    ensures MyApplet(this);
    @*/
    public MyApplet() 
    {
        //@ close MyApplet(this);
    }
    
    public static void install(byte[] array, short offset, byte length)
        //@ requires array != null &*& array_slice(array, 0, array.length, _) &*& 0 <= offset &*& offset + length <= array.length;
        //@ ensures static_MyApplet();
    {
        //@ open array_slice(array, 0, array.length, _);
        //@ close array_slice(array, 0, array.length, _);
        
        MyApplet theApplet = new MyApplet();
        
        byte iLen = array[offset]; 
        offset = (short)(offset + iLen + 1);
        
        byte cLen = array[offset]; 
        offset = (short)(offset + cLen + 1);
        
        byte aLen = array[offset]; 
        
        byte bLen = array[(short)(offset + 1)];
        
        if (bLen != 0) {
            someByteArray = new byte[bLen];
            //@ close array_slice(someByteArray, 0, bLen, _);
            //@ close static_MyApplet();
            
            theApplet.register();
            return;
        } else {
            ISOException.throwIt(ISO7816.SW_FUNC_NOT_SUPPORTED);
            //@ close static_MyApplet();
        }
    }
    
    public boolean select()
        //@ requires static_MyApplet();
        //@ ensures static_MyApplet() &*& result == true;
    {
        //@ open static_MyApplet();
        JCSystem.beginTransaction();
        
        //@ assert someByteArray |-> ?arr;
        //@ open array_slice(arr, 0, arr.length, _);
        someByteArray[17] = 42;
        //@ close array_slice(arr, 0, arr.length, _);
        
        JCSystem.commitTransaction();
        //@ close static_MyApplet();
        return true;
    }
    
    public void process(APDU apdu)
        //@ requires apdu != null &*& apdu.getBuffer |-> ?getBuffer &*& getBuffer != null;
        //@ ensures true;
    {
        byte[] buffer = apdu.getBuffer();
        //@ assume buffer != null;
        
        if (buffer[ISO7816.OFFSET_CLA] == (byte)0) {
            switch (buffer[ISO7816.OFFSET_INS]) {
                case ISO7816.INS_SELECT:
                    short length = apdu.setOutgoing();
                    byte[] replyData = new byte[10];
                    //@ close array_slice(replyData, 0, 10, _);
                    
                    if (length < 20) {
                        //@ open array_slice(replyData, 0, 10, _);
                        ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
                    }
                    apdu.setOutgoingLength((short)replyData.length);
                    apdu.sendBytesLong(replyData, (short)0, (short)replyData.length);
                    //@ open array_slice(replyData, 0, 10, _);
                    break;
            }
        }
    }
}