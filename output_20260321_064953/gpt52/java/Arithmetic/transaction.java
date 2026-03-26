import javacard.framework.*;

/*@
predicate MyApplet_state(MyApplet a; int tl, int tu) =
    a.tokensLeft |-> tl &*& a.tokensUsed |-> tu;
@*/

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    
    
    //@ requires this.tokensLeft |-> _ &*& this.tokensUsed |-> _;
    //@ ensures MyApplet_state(this, 10, 0);
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
    
    //@ requires MyApplet_state(this, ?tl, ?tu) &*& apdu != null;
    //@ ensures tl == 0 ? MyApplet_state(this, 0, tu) : MyApplet_state(this, tl - 1, tu + 1);
    public void process(APDU apdu)
        
        
    {
        
        //@ open MyApplet_state(this, tl, tu);
        if (tokensLeft == 0) {
            //@ close MyApplet_state(this, 0, tu);
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        }
        JCSystem.beginTransaction();
        
        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
        //@ close MyApplet_state(this, tl - 1, tu + 1);
    }
}