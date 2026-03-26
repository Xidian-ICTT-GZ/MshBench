import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    /*@
    predicate valid() = this.tokensLeft |-> ?tl &*& this.tokensUsed |-> ?tu &*& Applet.valid(this, _);
    @*/
    
    
    MyApplet()
        //@ requires true;
        //@ ensures valid();
        
        
    {
        tokensLeft = 10;
        //@ close valid();
    }
    
    public static void install(byte[] array, short offset, byte length) 
        //@ requires system();
        //@ ensures system();
        
        
    {
        MyApplet applet = new MyApplet();
        //@ open applet.valid();
        //@ close applet.valid();
        applet.register();
    }
    
    public void process(APDU apdu)
        //@ requires valid() &*& system();
        //@ ensures valid() &*& system();
        
        
    {
        //@ open valid();
        
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();
        
        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
        
        //@ close valid();
    }
}