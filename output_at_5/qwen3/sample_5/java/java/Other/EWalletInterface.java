package wallet;

import javacard.framework.*;

public interface EWalletInterface extends Shareable {

    //@ requires pincode != null &*& offset >= 0 &*& length > 0 &*& offset + length <= pincode.length;
    //@ ensures true;
    public void verify(byte[] pincode, short offset, byte length);
        
        
    
    //@ requires true;
    //@ ensures true;
    public void debit(byte amount);
        
        
    
}