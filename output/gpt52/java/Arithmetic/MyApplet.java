import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;

    /*@ predicate applet_state(MyApplet a; int left, int used) =
            a.tokensLeft |-> left &*& a.tokensUsed |-> used;
    @*/

    MyApplet()

    //@ requires this.tokensLeft |-> _ &*& this.tokensUsed |-> _;
    //@ ensures applet_state(this, 10, 0);
    {
        tokensLeft = 10;
    }

    public static void install(byte[] array, short offset, byte length)

    //@ requires true;
    //@ ensures true;
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }

    public void process(APDU apdu)

    //@ requires applet_state(this, ?left, ?used) &*& 0 < left;
    //@ ensures applet_state(this, left - 1, used + 1);
    {
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();

        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
    }
}