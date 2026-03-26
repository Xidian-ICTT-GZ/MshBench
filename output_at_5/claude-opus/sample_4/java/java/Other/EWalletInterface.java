package wallet;

import javacard.framework.*;

public interface EWalletInterface extends Shareable {

    //@ requires pincode != null &*& 0 <= offset &*& 0 <= length &*& offset + length <= pincode.length;
    //@ ensures true;
    void verify(byte[] pincode, short offset, byte length);
        
    //@ requires true;
    //@ ensures true;
    void debit(byte amount);
        
}