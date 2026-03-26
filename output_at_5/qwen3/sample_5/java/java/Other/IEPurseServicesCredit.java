package newepurse;

import javacard.framework.*;

public interface IEPurseServicesCredit extends Shareable {

    public void charge(short amount)
        //@ requires true;
        //@ ensures true;
    ;
        
        
    public void transaction(short amount)
        //@ requires true;
        //@ ensures true;
    ;
        
        

}