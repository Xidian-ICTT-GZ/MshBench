import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    /*@
    predicate this_tokens = this.tokensLeft |-> ?tl &*& this.tokensUsed |-> ?tu;
    @*/
    
    //@ requires true;
    //@ ensures this_tokens;
    MyApplet()
    //@ open this_tokens;
    {
        tokensLeft = 10;
        tokensUsed = 0;
    }
    
    //@ requires true;
    //@ ensures true;
    public static void install(byte[] array, short offset, byte length) 
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }
    
    //@ requires this_tokens;
    //@ ensures this_tokens;
    public void process(APDU apdu)
    //@ open this_tokens;
    {
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();
        
        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
    }
}