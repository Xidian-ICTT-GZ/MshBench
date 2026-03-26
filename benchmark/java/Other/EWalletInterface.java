package wallet;

import javacard.framework.*;

public interface EWalletInterface extends Shareable {

    public void verify(byte[] pincode, short offset, byte length);
        
        
    
    public void debit(byte amount);
        
        
    
}
