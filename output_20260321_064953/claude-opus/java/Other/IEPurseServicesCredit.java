package newepurse;

import javacard.framework.*;

/*@
predicate IEPurseServicesCredit_inv(ISEpurseServicesCredit obj;) = true;
@*/

public interface IEPurseServicesCredit extends Shareable {

    //@ public normal_behavior
    //@ requires IEPurseServicesCredit_inv(this);
    //@ ensures IEPurseServicesCredit_inv(this);
    public void charge(short amount);
        
    //@ public normal_behavior
    //@ requires IEPurseServicesCredit_inv(this);
    //@ ensures IEPurseServicesCredit_inv(this);
    public void transaction(short amount);
        
        

}