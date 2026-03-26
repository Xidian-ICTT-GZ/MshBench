package wallet;

import javacard.framework.*;

public interface EWalletInterface extends Shareable {

    //@ requires pincode != null &*& 0 <= offset &*& 0 <= length &*& (short)(offset + length) <= pincode.length;
    //@ ensures pincode != null &*& 0 <= offset &*& 0 <= length &*& (short)(offset + length) <= pincode.length;
    public void verify(byte[] pincode, short offset, byte length);

    //@ requires true;
    //@ ensures true;
    public void debit(byte amount);

}