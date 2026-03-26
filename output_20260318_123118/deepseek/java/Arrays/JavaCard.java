import javacard.framework.*;

public final class MyApplet extends Applet {
    static byte someByteArray[];
    
    //@ predicate MyAppletInv() = someByteArray |-> ?arr &*& (arr == null ? true : array_slice(arr, 0, arr.length, _));
    
    /*@
    predicate validArraySlice(byte[] a, short offset, byte length) =
        a != null &*& 0 <= offset &*& offset + length <= a.length &*& array_slice(a, offset, length, _);
    @*/
    
    public static void install(byte[] array, short offset, byte length)
        //@ requires validArraySlice(array, offset, length);
        //@ ensures true;
    {
        //@ open validArraySlice(array, offset, length);
        MyApplet theApplet = new MyApplet();
        //@ close theApplet.MyAppletInv();
        
        byte iLen = array[offset];
        //@ assert array_slice(array, offset, 1, _);
        offset = (short)(offset + iLen + 1);
        //@ assert 0 <= offset &*& offset <= array.length;
        
        byte cLen = array[offset];
        //@ assert array_slice(array, offset, 1, _);
        offset = (short)(offset + cLen + 1);
        //@ assert 0 <= offset &*& offset <= array.length;
        
        byte aLen = array[offset];
        //@ assert array_slice(array, offset, 1, _);
        
        byte bLen = array[(short)(offset + 1)];
        //@ assert array_slice(array, (short)(offset + 1), 1, _);
        
        if (bLen != 0) {
            someByteArray = new byte[bLen];
            //@ close MyAppletInv();
            
            theApplet.register();
            return;
        } else
            ISOException.throwIt(ISO7816.SW_FUNC_NOT_SUPPORTED);
    }
    
    public boolean select()
        //@ requires MyAppletInv();
        //@ ensures MyAppletInv() &*& result == true;
    {
        //@ open MyAppletInv();
        JCSystem.beginTransaction();
        
        //@ assert someByteArray |-> ?arr;
        //@ if (arr == null) { } else { array_slice_limits(arr); }
        someByteArray[17] = 42;
        
        JCSystem.commitTransaction();
        //@ close MyAppletInv();
        return true;
    }
    
    public void process(APDU apdu)
        //@ requires apdu != null;
        //@ ensures true;
    {
        byte[] buffer = apdu.getBuffer();
        //@ assume buffer != null;
        
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