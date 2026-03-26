package wallet;

import javacard.framework.*;

/*@ predicate valid_pin(byte[] pin, short offset, byte length) =
    offset >= 0 &*&
    length >= 0 &*&
    offset + length <= pin.length &*&
    length <= 8;
@*/

/*@ predicate authenticated() = true; // abstract authentication state @*/

public interface EWalletInterface extends Shareable {

    //@ requires [?f]pincode |-> ?contents &*& valid_pin(pincode, offset, length);
    //@ ensures authenticated();
    public void verify(byte[] pincode, short offset, byte length);
        
    //@ requires authenticated();
    //@ ensures true;
    public void debit(byte amount);
        
}