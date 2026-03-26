import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;

    /*@ predicate object_state(MyApplet this, int tokensLeft, int tokensUsed) =
          this.tokensLeft |-> tokensLeft &*& this.tokensUsed |-> tokensUsed;
    @*/

    //@ requires true;
    //@ ensures object_state(this, 10, 0);
    MyApplet()
    //@ ensures tokensLeft == 10 &*& tokensUsed == 0;
    {
        tokensLeft = 10;
        tokensUsed = 0;
    }

    //@ requires array != null &*& offset >= 0 &*& length >= 0 &*& offset + length <= array.length;
    //@ ensures true;
    public static void install(byte[] array, short offset, byte length)
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }

    //@ requires apdu != null &*& object_state(this, tokensLeft, tokensUsed);
    //@ ensures object_state(this, tokensLeft - 1, tokensUsed + 1) &*& tokensLeft > 0 &*& !\exceptional;
    //@ also
    //@ requires apdu != null &*& object_state(this, 0, tokensUsed);
    //@ ensures \exceptional;
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