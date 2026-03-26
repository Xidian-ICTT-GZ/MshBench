import javacard.framework.*;

/*@
predicate MyAppletInv(byte[] someByteArray) =
    someByteArray != null &*&
    array_slice(someByteArray, 0, someByteArray.length, _);
@*/

public final class MyApplet extends Applet {
    static byte someByteArray[];
    
    //@ static predicate MyAppletClassInv() = someByteArray == null ? true : MyAppletInv(someByteArray);

    public static void install(byte[] array, short offset, byte length)
        //@ requires true;
        //@ ensures true;
    {
        //@ close MyAppletClassInv();
        
        MyApplet theApplet = new MyApplet();
        
        byte iLen = array[offset]; 
        offset = (short)(offset + iLen + 1);
        
        byte cLen = array[offset]; 
        offset = (short)(offset + cLen + 1);
        
        byte aLen = array[offset]; 
        
        byte bLen = array[(short)(offset + 1)];
        
        if (bLen != 0) {
            someByteArray = new byte[bLen];
            //@ close MyAppletInv(someByteArray);
            //@ close theApplet.MyAppletPred();
            
            theApplet.register();
            return;
        } else
            ISOException.throwIt(ISO7816.SW_FUNC_NOT_SUPPORTED); 
    }
    
    //@ predicate MyAppletPred() = true;
    
    public boolean select()
        //@ requires MyAppletPred();
        //@ ensures MyAppletPred() &*& result == true;
    {
        JCSystem.beginTransaction();
        
        //@ open MyAppletClassInv();
        //@ open MyAppletInv(someByteArray);
        someByteArray[17] = 42; 
        //@ close MyAppletInv(someByteArray);
        //@ close MyAppletClassInv();
        
        JCSystem.commitTransaction();
        return true;
    }
    
    public void process(APDU apdu)
        //@ requires MyAppletPred();
        //@ ensures MyAppletPred();
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