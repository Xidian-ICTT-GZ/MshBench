package wallet;

import javacard.framework.*;

public interface EWalletInterface extends Shareable {

    void verify(byte[] pincode, short offset, byte length);

    void debit(byte amount);

}