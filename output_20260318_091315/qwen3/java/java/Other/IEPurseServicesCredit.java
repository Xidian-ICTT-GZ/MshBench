package newepurse;

import javacard.framework.*;

/*@ predicate purse_state(short balance) = true; @*/

public interface IEPurseServicesCredit extends Shareable {

    //@ requires purse_state(?b) &*& amount >= 0 &*& b + amount <= 32767;
    //@ ensures purse_state(b + amount);
    public void charge(short amount);
        
        
    //@ requires purse_state(?b) &*& amount >= 0 &*& b >= amount;
    //@ ensures purse_state(b - amount);
    public void transaction(short amount);
        
        

}