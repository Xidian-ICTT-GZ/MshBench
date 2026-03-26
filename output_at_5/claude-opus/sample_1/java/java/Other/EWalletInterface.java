package wallet;

import javacard.framework.*;

public interface EWalletInterface extends Shareable {

    //@ requires pincode != null &*& 0 <= offset &*& offset + length <= pincode.length &*& length >= 0;
    //@ ensures true;
    public void verify(byte[] pincode, short offset, byte length);
        
    //@ requires true;
    //@ ensures true;
    public void debit(byte amount);
        
}