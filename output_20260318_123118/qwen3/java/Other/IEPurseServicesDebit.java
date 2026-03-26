package newepurse;

import javacard.framework.*;

/*@ predicate purse_state(short balance) = true; @*/

public interface IEPurseServicesDebit extends Shareable {

    //@ requires purse_state(balance) &*& amount >= 0 &*& balance >= amount;
    //@ ensures purse_state(old_balance - amount);
    public void debit(short amount) throws ISOException ;
        
        

}