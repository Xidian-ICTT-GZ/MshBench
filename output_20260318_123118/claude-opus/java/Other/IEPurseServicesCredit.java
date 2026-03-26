package newepurse;

import javacard.framework.*;

public interface IEPurseServicesCredit extends Shareable {

    //@ public normal_behavior
    //@ requires amount >= 0;
    //@ ensures true;
    public void charge(short amount);
        
        
    //@ public normal_behavior
    //@ requires amount >= 0;
    //@ ensures true;
    public void transaction(short amount);
        
        

}