import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;

    /*@ predicate tokens_state(int left, int used) = 
          this.tokensLeft |-> left &*& this.tokensUsed |-> used;
    @*/

    //@ requires this.tokensLeft |-> _;
    //@ ensures this.tokensLeft |-> 10 &*& this.tokensUsed |-> 0;
    MyApplet()
    {
        tokensLeft = 10;
    }

    //@ requires true;
    //@ ensures true;
    public static void install(byte[] array, short offset, byte length) 
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }

    //@ requires tokens_state(?left, ?used) &*& left > 0;
    //@ ensures tokens_state(left - 1, used + 1);
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