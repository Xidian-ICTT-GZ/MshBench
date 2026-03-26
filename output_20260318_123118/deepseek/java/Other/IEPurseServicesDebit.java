package newepurse;

import javacard.framework.*;

public interface IEPurseServicesDebit extends Shareable {

    //@ predicate valid() = true;
    
    /*@
    predicate predebit(short amount) =
        valid()
        &*& amount >= 0
        &*& amount <= 32767;
    @*/
    
    /*@
    predicate postdebit() =
        valid();
    @*/
    
    public void debit(short amount) throws ISOException ;
    //@ requires predebit(amount);
    //@ ensures postdebit();
        
        

}