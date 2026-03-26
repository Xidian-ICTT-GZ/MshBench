import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;

    /*@ predicate MyAppletInv(MyApplet a;) = 
          a.tokensLeft |-> ?tl &*& a.tokensUsed |-> ?tu;
    @*/

    //@ requires true;
    //@ ensures MyAppletInv(this) &*& tokensLeft == 10 &*& tokensUsed == 0;
    MyApplet()
    //@ object_ctor(this);
    {
        tokensLeft = 10;
    }

    //@ requires array != null &*& offset >= 0 &*& length >= 0 &*& offset + length <= array.length;
    //@ ensures true;
    public static void install(byte[] array, short offset, byte length)
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }

    //@ requires this.tokensLeft >= 0 &*& this.tokensUsed >= 0 &*& apdu != null &*& MyAppletInv(this);
    /*@ ensures
          ((\old(this.tokensLeft) > 0) &*& 
             this.tokensLeft == \old(this.tokensLeft) - 1 &*&
             this.tokensUsed == \old(this.tokensUsed) + 1 &*&
             !\exceptional) 
          ||
          ((\old(this.tokensLeft) == 0) &*& \exceptional &*&
             this.tokensLeft == 0 &*&
             this.tokensUsed == \old(this.tokensUsed));
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