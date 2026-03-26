import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    //@ predicate MyApplet() = tokensLeft |-> ?tl &*& tokensUsed |-> ?tu;
    //@ predicate MyAppletInv() = tokensLeft |-> ?tl &*& tokensUsed |-> ?tu &*& tl >= 0;
    
    MyApplet()
        //@ requires true;
        //@ ensures MyAppletInv();
    {
        tokensLeft = 10;
        //@ close MyApplet();
        //@ close MyAppletInv();
    }
    
    public static void install(byte[] array, short offset, byte length) 
        //@ requires true;
        //@ ensures true;
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }
    
    public void process(APDU apdu)
        //@ requires MyAppletInv();
        //@ ensures MyAppletInv();
    {
        //@ open MyAppletInv();
        //@ open MyApplet();
        
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();
        
        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
        
        //@ close MyApplet();
        //@ close MyAppletInv();
    }
}