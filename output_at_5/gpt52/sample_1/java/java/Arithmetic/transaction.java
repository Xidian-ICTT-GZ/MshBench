import javacard.framework.*;

/*@
predicate MyApplet_state(MyApplet a; int left, int used) =
    a.tokensLeft |-> left &*& a.tokensUsed |-> used;
@*/

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    
    
    MyApplet()
        //@ requires this.tokensLeft |-> _ &*& this.tokensUsed |-> _;
        //@ ensures MyApplet_state(this, 10, 0);
        
    {
        tokensLeft = 10;
    }
    
    public static void install(byte[] array, short offset, byte length) 
        //@ requires true;
        //@ ensures true;
        
        
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }
    
    public void process(APDU apdu)
        //@ requires MyApplet_state(this, ?left, ?used);
        //@ ensures left == 0 ? MyApplet_state(this, left, used) : MyApplet_state(this, left - 1, used + 1);
        
        
    {
        //@ open MyApplet_state(this, left, used);
        
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();
        
        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
        
        //@ close MyApplet_state(this, left - 1, used + 1);
    }
}