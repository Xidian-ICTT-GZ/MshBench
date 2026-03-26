package newepurse;

import javacard.framework.*;

public interface IEPurseServicesDebit extends Shareable {

    //@ requires amount >= 0 &*& amount <= 32767; 
    //@ ensures true;
    public void debit(short amount) throws ISOException ;
        
        

}