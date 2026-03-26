import javacard.framework.*;

/*@
predicate MyApplet_inv(MyApplet a;) =
    a.tokensLeft |-> ?tl &*& a.tokensUsed |-> ?tu &*& tl >= 0 &*& tu >= 0;
@*/

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;

    //@ ensures MyApplet_inv(this);
    MyApplet()
    {
        tokensLeft = 10;
        tokensUsed = 0;
        //@ close MyApplet_inv(this);
    }

    //@ ensures true;
    public static void install(byte[] array, short offset, byte length)
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }

    //@ requires MyApplet_inv(this);
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