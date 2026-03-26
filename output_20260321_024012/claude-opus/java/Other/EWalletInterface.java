package wallet;

import javacard.framework.*;

public interface EWalletInterface extends Shareable {

    /*@
    // No fields to own in interface, so minimal contracts
    @*/
    public void verify(byte[] pincode, short offset, byte length);
        
    /*@
    // Minimal contract stating method is allowed to be called
    @*/
    public void debit(byte amount);
        
}