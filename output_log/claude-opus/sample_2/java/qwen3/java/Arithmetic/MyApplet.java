import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;

    /*@ predicate valid_app() = this.tokensLeft |-> ?tl &*& this.tokensUsed |-> ?tu &*& tl >= 0 &*& tu >= 0; @*/

    //@ ensures tokensLeft == 10 &*& tokensUsed == 0;
    MyApplet()
        //@ requires true;
        //@ ensures valid_app() &*& tokensLeft == 10 &*& tokensUsed == 0;
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

    //@ requires apdu != null &*& valid_app() &*& tokensLeft >= 0 &*& tokensUsed >= 0 &*& this.tokensLeft == tokensLeft &*& this.tokensUsed == tokensUsed;
    /*@
    ensures tokensLeft > 0 ==>
                valid_app() &*&
                tokensLeft == \old(tokensLeft) - 1 &*&
                tokensUsed == \old(tokensUsed) + 1;
    ensures tokensLeft == 0 ==>
                false; // method throws exception and does not return normally
    @*/
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