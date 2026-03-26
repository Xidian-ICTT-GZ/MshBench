package newepurse;

import javacard.framework.*;

public interface IEPurseServicesCredit extends Shareable {

    //@ predicate IEPurseServicesCredit() = true;
    
    public void charge(short amount);
    //@ requires IEPurseServicesCredit();
    //@ ensures IEPurseServicesCredit();
        
    public void transaction(short amount);
    //@ requires IEPurseServicesCredit();
    //@ ensures IEPurseServicesCredit();
        
        

}