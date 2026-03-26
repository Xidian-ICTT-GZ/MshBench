import javacard.framework.*;

/*@
predicate myApplet(int tokensLeft, int tokensUsed) = true;
@*/

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    
    
    //@ requires true;
    //@ ensures true;
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
    
    //@ requires this |-> myApplet(tokensLeft, tokensUsed);
    //@ ensures this |-> myApplet(tokensLeft - 1, tokensUsed + 1);
    public void process(APDU apdu)
        
        
    {
        
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();
        //@ open myApplet(tokensLeft, tokensUsed);
        tokensLeft--;
        tokensUsed++;
        //@ close myApplet(tokensLeft, tokensUsed);
        JCSystem.commitTransaction();
    }
}