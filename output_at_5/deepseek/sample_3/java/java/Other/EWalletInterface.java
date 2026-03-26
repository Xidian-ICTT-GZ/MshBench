package wallet;

import javacard.framework.*;

public interface EWalletInterface extends Shareable {

    //@ requires true;
    //@ ensures true;
    public void verify(byte[] pincode, short offset, byte length);
        
        
    
    //@ requires true;
    //@ ensures true;
    public void debit(byte amount);
        
        
    
}