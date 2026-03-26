package subpackage;

/*@
predicate Interface1_inv(Interface1 i) = true;
predicate Subpackage_inv(Subpackage s) = true;
@*/

interface Interface1
{
}

public class Subpackage implements Interface1
{
    //@ requires true;
    //@ ensures Subpackage_inv(this);
    public Subpackage()
    {
        //@ close Subpackage_inv(this);
    }
}