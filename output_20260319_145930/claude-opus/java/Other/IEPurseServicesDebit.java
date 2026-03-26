package newepurse;

import javacard.framework.*;

public interface IEPurseServicesDebit extends Shareable {

    //@ requires true;
    //@ ensures true;
    public void debit(short amount) throws ISOException ;

}