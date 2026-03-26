import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    
    
    MyApplet()
        
        
    {
        tokensLeft = 10;
    }
    
    public static void install(byte[] array, short offset, byte length) 
        
        
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }
    
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