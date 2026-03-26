import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;

    //@ true;
    //@ ensures tokensLeft == 10 &*& tokensUsed == 0;
    MyApplet()
    {
        tokensLeft = 10;
    }

    //@ requires array != null &*& offset >= 0 &*& length >= 0 &*& offset + length <= array.length;
    //@ ensures true;
    public static void install(byte[] array, short offset, byte length)
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }

    //@ requires apdu != null &*& tokensLeft >= 0 &*& tokensUsed >= 0;
    //@ ensures tokensLeft == \old(tokensLeft) - (1 &*& \old(tokensLeft) > 0) &*&
    //         tokensUsed == \old(tokensUsed) + (1 &*& \old(tokensLeft) > 0) &*&
    //         (\old(tokensLeft) == 0 ==> \exceptional);
    //@ behavior exceptional:
    //@   assumes \old(tokensLeft) == 0;
    //@   ensures \exceptional;
    public void process(APDU apdu)
    {
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();

        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
    }
}