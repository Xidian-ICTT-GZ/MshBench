import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;

    /*@ predicate MyAppletInv(MyApplet a) = 
          a.tokensLeft |-> ?tl &*& a.tokensUsed |-> ?tu &*&
          tl >= 0 &*& tu >= 0;
    @*/

    //@ requires true;
    //@ ensures MyAppletInv(this) &*& tokensLeft == 10 &*& tokensUsed == 0;
    MyApplet()
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

    //@ requires apdu != null &*& MyAppletInv(this) &*& tokensLeft >= 0 &*& tokensUsed >= 0;
    /*@ ensures (tokensLeft == \old(tokensLeft) - 1 &*& tokensUsed == \old(tokensUsed) + 1) || 
               (tokensLeft == 0 &*& tokensUsed == \old(tokensUsed)) &*&
               (tokensLeft > 0 ==> !\exceptional) &*&
               (tokensLeft == 0 ==> \exceptional) &*&
               MyAppletInv(this);
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