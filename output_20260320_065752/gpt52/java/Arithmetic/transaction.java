import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    /*@
    predicate myapplet_state(MyApplet a; int left, int used) =
        a.tokensLeft |-> left &*& a.tokensUsed |-> used;
    @*/
    
    //@ predicate valid(MyApplet a) = myapplet_state(a, ?left, ?used);
    
    MyApplet()
        //@ requires this.tokensLeft |-> _ &*& this.tokensUsed |-> _;
        //@ ensures valid(this);
        
    {
        tokensLeft = 10;
        //@ close valid(this);
    }
    
    public static void install(byte[] array, short offset, byte length) 
        //@ requires true;
        //@ ensures true;
        
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }
    
    public void process(APDU apdu)
        //@ requires valid(this);
        //@ ensures valid(this);
        
    {
        //@ open valid(this);
        
        if (tokensLeft == 0) {
            //@ close valid(this);
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        }
        JCSystem.beginTransaction();
        
        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
        
        //@ close valid(this);
    }
}