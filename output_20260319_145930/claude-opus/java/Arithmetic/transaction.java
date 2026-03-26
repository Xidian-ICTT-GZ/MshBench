import javacard.framework.*;

/*@
predicate MyApplet_inv(MyApplet a;) =
    a.tokensLeft |-> ?tl &*& a.tokensUsed |-> ?tu;
@*/

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    
    
    MyApplet()
        //@ requires true;
        //@ ensures MyApplet_inv(this);
    {
        tokensLeft = 10;
        //@ close MyApplet_inv(this);
    }
    
    public static void install(byte[] array, short offset, byte length) 
        //@ requires array != null;
        //@ ensures true;
    {
        MyApplet applet = new MyApplet();
        //@ open MyApplet_inv(applet);
        applet.register();
    }
    
    public void process(APDU apdu)
        //@ requires MyApplet_inv(this);
        //@ ensures MyApplet_inv(this);
    {
        //@ open MyApplet_inv(this);
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();
        
        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
        //@ close MyApplet_inv(this);
    }
}