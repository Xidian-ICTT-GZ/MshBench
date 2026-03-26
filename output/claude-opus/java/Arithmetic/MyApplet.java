import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;

    /*@
    predicate valid() =
        this.tokensLeft |-> ?tl &*& this.tokensUsed |-> ?tu &*&
        tl >= 0 &*& tu >= 0 &*& tl + tu == 10;
    @*/

    //@ requires true;
    //@ ensures valid();
    MyApplet()

    {
        tokensLeft = 10;
        //@ close valid();
    }

    //@ requires array != null &*& array.length |-> ?len &*& offset >= 0 &*& length >= 0;
    //@ ensures true;
    public static void install(byte[] array, short offset, byte length)

    {
        MyApplet applet = new MyApplet();
        applet.register();
        //@ leak applet.valid();
    }

    //@ requires valid() &*& apdu != null;
    //@ ensures valid();
    public void process(APDU apdu)

    {
        //@ open valid();
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();

        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
        //@ close valid();
    }
}