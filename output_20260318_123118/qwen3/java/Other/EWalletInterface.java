package wallet;

import javacard.framework.*;

/*@ predicate valid_pin(byte[] pin, short offset, byte len) =
    pin != null &*&
    offset >= 0 &*&
    len > 0 &*&
    (offset + len) <= pin.length;
@*/

/*@ predicate authenticated() = true; // abstract authentication state @*/

public interface EWalletInterface extends Shareable {

    //@ requires valid_pin(pincode, offset, length);
    //@ ensures true;
    public void verify(byte[] pincode, short offset, byte length);
        
    //@ requires authenticated();
    //@ ensures true;
    public void debit(byte amount);
        
}