package newepurse;

import javacard.framework.*;

/*@
predicate IEPurseServicesDebit_inv();
@*/
public interface IEPurseServicesDebit extends Shareable {

    /*@ 
    // No state to track in interface predicate.
    @*/
    //@ requires true;
    //@ ensures true;
    public void debit(short amount) throws ISOException ;
        
        

}