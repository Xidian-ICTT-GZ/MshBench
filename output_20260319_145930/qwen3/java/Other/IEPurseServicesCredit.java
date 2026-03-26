package newepurse;

import javacard.framework.*;

public interface IEPurseServicesCredit extends Shareable {

    //@ requires true;
    public void charge(short amount);
        
        
    //@ requires true;
    public void transaction(short amount);
        
        

}