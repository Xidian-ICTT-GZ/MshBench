import javacard.framework.*;

/*@
predicate MyApplet_inv(MyApplet a;) =
    a.tokensLeft |-> ?tl &*& a.tokensUsed |-> ?tu &*& tl >= 0 &*& tu >= 0;
@*/

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;

    //@ requires true;
    //@ ensures MyApplet_inv(this);
    MyApplet()
    {
        tokensLeft = 10;
        //@ close MyApplet_inv(this);
    }

    //@ requires array != null &*& array.length >= offset + length &*& offset >= 0 &*& length >= 0;
    //@ ensures true;
    public static void install(byte[] array, short offset, byte length)
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }

    //@ requires MyApplet_inv(this) &*& apdu != null;
    //@ ensures MyApplet_inv(this);
    public void process(APDU apdu)
    {
        //@ open MyApplet_inv(this);
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();

        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
        //@ close MyApplet_inv(this);
    }
}