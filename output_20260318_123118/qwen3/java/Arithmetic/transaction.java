/*@ predicate applet_state(MyApplet a; int left, int used) =
    a.tokensLeft |-> left &*& a.tokensUsed |-> used;
@*/

import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    
    
    //@ requires true;
    //@ ensures applet_state(this, 10, 0);
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
    
    //@ requires applet_state(this, ?left, ?used) &*& left > 0;
    //@ ensures applet_state(this, left - 1, used + 1);
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