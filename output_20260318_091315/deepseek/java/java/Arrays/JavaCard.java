import javacard.framework.*;

public final class MyApplet extends Applet {
    static byte someByteArray[];

    //@ predicate MyApplet() = true;

    //@ requires array != null &*& 0 <= offset &*& offset + length <= array.length &*& length >= 0;
    //@ ensures true;
    public static void install(byte[] array, short offset, byte length)
    {
        //@ close MyApplet();
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
            theApplet.register();
            return;
        } else
            ISOException.throwIt(ISO7816.SW_FUNC_NOT_SUPPORTED);
    }

    //@ predicate array_slice(byte[] a, int start, int end, list<byte> contents) = a != null &*& 0 <= start &*& start <= end &*& end <= a.length &*& array_slice_char(a, start, end, contents);
    //@ predicate array_slice_char(byte[] a, int start, int end, list<byte> contents);

    //@ requires array_slice(someByteArray, 0, someByteArray.length, _);
    //@ ensures array_slice(someByteArray, 0, someByteArray.length, _) &*& result == true;
    public boolean select()
    {
        JCSystem.beginTransaction();

        //@ open array_slice(someByteArray, 0, someByteArray.length, _);
        //@ open array_slice_char(someByteArray, 0, someByteArray.length, _);
        someByteArray[17] = 42;
        //@ close array_slice_char(someByteArray, 0, someByteArray.length, _);
        //@ close array_slice(someByteArray, 0, someByteArray.length, _);

        JCSystem.commitTransaction();
        return true;
    }

    //@ requires apdu != null;
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