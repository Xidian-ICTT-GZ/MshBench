package newepurse;

import javacard.framework.*;

public interface IEPurseServicesDebit extends Shareable {

    //@ predicate valid() = true;
    
    /*@
    @ requires valid();
    @ ensures valid();
    @*/
    public void debit(short amount) throws ISOException ;
        
        

}