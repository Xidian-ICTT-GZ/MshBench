import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;

    //@ predicate MyApplet() = tokensLeft |-> ?tl &*& tokensUsed |-> ?tu &*& tl >= 0 &*& tu >= 0;
    //@ predicate MyApplet_transaction() = tokensLeft |-> ?tl &*& tokensUsed |-> ?tu &*& tl >= 0 &*& tu >= 0;

    MyApplet()
    //@ requires true;
    //@ ensures MyApplet();
    {
        tokensLeft = 10;
        //@ close MyApplet();
    }

    public static void install(byte[] array, short offset, byte length)
    //@ requires true;
    //@ ensures true;
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }

    public void process(APDU apdu)
    //@ requires MyApplet();
    //@ ensures MyApplet();
    {
        //@ open MyApplet();
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();
        //@ close MyApplet_transaction();

        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
        //@ open MyApplet_transaction();
        //@ close MyApplet();
    }
}