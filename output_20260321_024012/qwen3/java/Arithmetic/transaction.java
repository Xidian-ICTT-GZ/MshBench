import javacard.framework.*;

/*@
predicate myapplet_state(MyApplet a; int left, int used) =
    a.tokensLeft |-> left &*& a.tokensUsed |-> used;
@*/

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    
    
    //@ requires true;
    //@ ensures myapplet_state(this, 10, 0);
    MyApplet()
        
        
    {
        tokensLeft = 10;
        //@ close myapplet_state(this, 10, 0);
    }
    
    //@ requires true;
    //@ ensures true;
    public static void install(byte[] array, short offset, byte length) 
        
        
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }
    
    //@ requires myapplet_state(this, ?left, ?used) &*& left > 0;
    //@ ensures myapplet_state(this, left - 1, used + 1);
    public void process(APDU apdu)
        
        
    {
        //@ open myapplet_state(this, ?l, ?u);
        
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();
        
        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
        //@ close myapplet_state(this, l - 1, u + 1);
    }
}