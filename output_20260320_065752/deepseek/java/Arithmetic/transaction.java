import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    /*@
    predicate MyApplet() = 
        tokensLeft |-> ?tl &*& tokensUsed |-> ?tu;
    @*/
    
    MyApplet()
        //@ requires true;
        //@ ensures MyApplet();
    {
        tokensLeft = 10;
        tokensUsed = 0;
        //@ close MyApplet();
    }
    
    public static void install(byte[] array, short offset, byte length) 
        //@ requires true;
        //@ ensures true;
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }
    
    public void process(APDU apdu)
        //@ requires MyApplet();
        //@ ensures MyApplet();
    {
        //@ open MyApplet();
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();
        
        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
        //@ close MyApplet();
    }
}