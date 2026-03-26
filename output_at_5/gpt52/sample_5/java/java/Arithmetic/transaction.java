import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    /*@
    predicate valid() = this.tokensLeft |-> ?tl &*& this.tokensUsed |-> ?tu;
    @*/
    
    
    
    MyApplet()
        //@ requires true;
        //@ ensures valid();
        
        
    {
        tokensLeft = 10;
        //@ close valid();
    }
    
    public static void install(byte[] array, short offset, byte length) 
        //@ requires true;
        //@ ensures true;
        
        
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }
    
    public void process(APDU apdu)
        //@ requires this.tokensLeft |-> ?tl &*& this.tokensUsed |-> ?tu;
        //@ ensures this.tokensLeft |-> ?tl2 &*& this.tokensUsed |-> ?tu2;
        
        
    {
        
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();
        
        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
    }
}