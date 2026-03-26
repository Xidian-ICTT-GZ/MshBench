import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    /*@
    predicate Tokens(int self) = true;
    @*/
    
    MyApplet()
        
        //@ requires true;
        //@ ensures Tokens(this);
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
        
        //@ requires true;
        //@ ensures Tokens(this);
    {
        
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();
        
        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
    }
}