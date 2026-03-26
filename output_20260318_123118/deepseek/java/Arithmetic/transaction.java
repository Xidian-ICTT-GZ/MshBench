import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;

    //@ predicate valid() = tokensLeft |-> ?tl &*& tokensUsed |-> ?tu &*& tl >= 0 &*& tu >= 0 &*& tl + tu == 10;

    MyApplet()
    //@ requires true;
    //@ ensures valid();
    {
        tokensLeft = 10;
        //@ close valid();
    }

    public static void install(byte[] array, short offset, byte length)
    //@ requires true;
    //@ ensures true;
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }

    public void process(APDU apdu)
    //@ requires valid();
    //@ ensures valid();
    {
        //@ open valid();
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();
        //@ int tl = tokensLeft;
        //@ int tu = tokensUsed;
        //@ assert tl >= 1 &*& tu >= 0 &*& tl + tu == 10;
        tokensLeft--;
        tokensUsed++;
        //@ close valid();
        JCSystem.commitTransaction();
    }
}