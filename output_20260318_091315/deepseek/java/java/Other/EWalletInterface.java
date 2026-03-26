package wallet;

import javacard.framework.*;

public interface EWalletInterface extends Shareable {

    /*@
    predicate valid() = true;
    @*/

    //@ requires pincode != null &*& array_slice(pincode, offset, length, _);
    //@ ensures true;
    public void verify(byte[] pincode, short offset, byte length);
        
        
    
    //@ requires true;
    //@ ensures true;
    public void debit(byte amount);
        
        
    
}