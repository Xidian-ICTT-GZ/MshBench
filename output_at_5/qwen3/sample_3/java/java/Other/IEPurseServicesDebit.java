package newepurse;

import javacard.framework.*;

public interface IEPurseServicesDebit extends Shareable {

    public void debit(short amount) throws ISOException ;
        
        

}