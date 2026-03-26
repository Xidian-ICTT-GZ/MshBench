package newepurse;

import javacard.framework.*;

/*@
predicate IEPurseServicesCredit_inv(IEPurseServicesCredit obj) = true;
@*/

public interface IEPurseServicesCredit extends Shareable {

    //@ public abstract
    //@ requires IEPurseServicesCredit_inv(this);
    //@ ensures IEPurseServicesCredit_inv(this);
    public void charge(short amount);
        
    //@ public abstract
    //@ requires IEPurseServicesCredit_inv(this);
    //@ ensures IEPurseServicesCredit_inv(this);
    public void transaction(short amount);
        
        

}