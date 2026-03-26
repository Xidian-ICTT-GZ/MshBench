package wallet;

import javacard.framework.*;

public interface EWalletInterface extends Shareable {

    //@ // predicate valid();
    //@ // requires valid();
    //@ // ensures valid();
    public void verify(byte[] pincode, short offset, byte length);
        
        
    
    //@ // predicate valid();
    //@ // requires valid();
    //@ // ensures valid();
    public void debit(byte amount);
        
        
    
}