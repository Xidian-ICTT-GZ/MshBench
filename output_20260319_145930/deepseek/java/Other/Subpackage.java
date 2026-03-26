package subpackage;

//@ predicate Interface1(Interface1 i) = true;

interface Interface1
{
}

public class Subpackage implements Interface1
{
    //@ predicate Subpackage() = true;
    
    //@ requires true;
    //@ ensures Subpackage();
    public Subpackage()
    //@ ensures Subpackage();
    {
        //@ close Subpackage();
    }
}