import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    /*@ predicate inv() =
            this.tokensLeft |-> ?tl &*& this.tokensUsed |-> ?tu &*& 0 <= tl;
    @*/
    
    //@ requires true;
    //@ ensures inv();
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
    
    //@ requires inv();
    //@ ensures inv();
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