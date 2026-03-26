import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    /*@
    predicate MyAppletInv(MyApplet this) = 
        this.tokensLeft |-> ?tl &*& this.tokensUsed |-> ?tu;
    @*/
    
    /*@
    requires true;
    ensures MyAppletInv(this);
    @*/
    MyApplet()
    {
        tokensLeft = 10;
        tokensUsed = 0;
        //@ close MyAppletInv(this);
    }
    
    //@ requires true;
    //@ ensures true;
    public static void install(byte[] array, short offset, byte length) 
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }
    
    //@ requires MyAppletInv(this);
    //@ ensures MyAppletInv(this);
    public void process(APDU apdu)
    {
        //@ open MyAppletInv(this);
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();
        
        tokensLeft--;
        tokensUsed++;
        
        JCSystem.commitTransaction();
        //@ close MyAppletInv(this);
    }
}