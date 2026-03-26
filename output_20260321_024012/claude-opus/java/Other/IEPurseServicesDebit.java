package newepurse;

import javacard.framework.*;

/*@
predicate IEPurseServicesDebit_obj(IEPurseServicesDebit o) = true;
@*/

public interface IEPurseServicesDebit extends Shareable {

    /*@
    @ public normal_behavior
    @ requires IEPurseServicesDebit_obj(this);
    @ ensures IEPurseServicesDebit_obj(this);
    @*/
    public void debit(short amount) throws ISOException ;
        
        

}