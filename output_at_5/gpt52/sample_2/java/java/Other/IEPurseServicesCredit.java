package newepurse;

import javacard.framework.*;

public interface IEPurseServicesCredit extends Shareable {

    public void charge(short amount);
        
        
    public void transaction(short amount);
        
        

}