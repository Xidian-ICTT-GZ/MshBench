package newepurse;

import javacard.framework.*;

public interface IEPurseServicesCredit extends Shareable {

    //@ requires amount >= 0;
    //@ ensures true;
    public void charge(short amount);
        
        
    //@ requires amount >= 0;
    //@ ensures true;
    public void transaction(short amount);
        
        

}