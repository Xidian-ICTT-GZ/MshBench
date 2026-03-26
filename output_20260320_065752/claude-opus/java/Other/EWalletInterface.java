package wallet;

import javacard.framework.*;

/*@
predicate EWalletInterfaceInv(EWalletInterface ewi) = true;
@*/

public interface EWalletInterface extends Shareable {

    //@ requires EWalletInterfaceInv(this) &*& pincode != null &*& 0 <= offset &*& offset + length <= pincode.length;
    //@ ensures EWalletInterfaceInv(this);
    public void verify(byte[] pincode, short offset, byte length);
    
    //@ requires EWalletInterfaceInv(this);
    //@ ensures EWalletInterfaceInv(this);
    public void debit(byte amount);
    
}