package newepurse;

import javacard.framework.*;

public interface IEPurseServicesCredit extends Shareable {

    //@ public boolean charge_valid;
    //@ requires charge_valid &*& amount > (short)0;
    //@ ensures charge_valid == true;
    public void charge(short amount);
        
        
    //@ public boolean transaction_valid;
    //@ requires transaction_valid &*& amount >= (short)0;
    //@ ensures transaction_valid == true;
    public void transaction(short amount);
        
        

}