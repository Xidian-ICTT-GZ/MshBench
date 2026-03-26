package wallet;

import javacard.framework.*;

public interface EWalletInterface extends Shareable {

    //@ predicate valid() = true;
    
    public void verify(byte[] pincode, short offset, byte length);
    //@ requires valid() &*& array_slice(pincode, offset, length, _);
    //@ ensures valid();
        
        
    
    public void debit(byte amount);
    //@ requires valid();
    //@ ensures valid();
        
        
    
}