import javacard.framework.*;

/*@ predicate myapplet(MyApplet a, int left, int used) =
    a.tokensLeft |-> left &*& a.tokensUsed |-> used;
@*/

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    
    
    //@ requires true;
    //@ ensures myapplet(this, 10, 0);
    MyApplet()
        
        
    {
        tokensLeft = 10;
        tokensUsed = 0;
        //@ close myapplet(this, 10, 0);
    }
    
    //@ requires true;
    //@ ensures true;
    public static void install(byte[] array, short offset, byte length) 
        
        
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }
    
    //@ requires myapplet(this, ?left, ?used);
    //@ ensures myapplet(this, left - 1, used + 1) &*& left > 0;
    public void process(APDU apdu)
        
        
    {
        
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        //@ open myapplet(this, _, _);
        JCSystem.beginTransaction();
        
        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
        //@ close myapplet(this, tokensLeft, tokensUsed);
    }
}