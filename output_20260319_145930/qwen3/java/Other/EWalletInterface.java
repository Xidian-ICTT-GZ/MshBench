package wallet;

import javacard.framework.*;

public interface EWalletInterface extends Shareable {

    //@ requires true;
    public void verify(byte[] pincode, short offset, byte length);
        
        
    
    //@ requires true;
    public void debit(byte amount);
        
        
    
}