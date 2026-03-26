import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    //@ predicate valid() = tokensLeft |-> ?tl &*& tokensUsed |-> ?tu &*& tl >= 0 &*& tu >= 0;
    
    MyApplet()
    //@ requires true;
    //@ ensures valid() &*& tokensLeft == 10 &*& tokensUsed == 0;
    {
        tokensLeft = 10;
        tokensUsed = 0;
    }
    
    public static void install(byte[] array, short offset, byte length) 
    //@ requires true;
    //@ ensures true;
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }
    
    public void process(APDU apdu)
    //@ requires valid();
    //@ ensures valid();
    {
        //@ open valid();
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        //@ assert tokensLeft > 0;
        JCSystem.beginTransaction();
        //@ close valid();
        
        tokensLeft--;
        tokensUsed++;
        //@ open valid();
        //@ close valid();
        JCSystem.commitTransaction();
        //@ close valid();
    }
}