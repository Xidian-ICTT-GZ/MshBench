import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    /*@
      predicate object_inv(MyApplet this) = 
        this.tokensLeft |-> ?tokensLeft &*&
        this.tokensUsed |-> ?tokensUsed;
    @*/
    
    //@ requires true;
    //@ ensures object_inv(this);
    MyApplet()
    //@ requires true;
    //@ ensures object_inv(this);
    {
        tokensLeft = 10;
        tokensUsed = 0;
    }
    
    //@ requires true;
    //@ ensures true;
    public static void install(byte[] array, short offset, byte length) 
    //@ requires true;
    //@ ensures true;
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }
    
    //@ requires object_inv(this);
    //@ ensures object_inv(this);
    public void process(APDU apdu)
    //@ requires object_inv(this);
    //@ ensures object_inv(this);
    {
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();
        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
    }
}