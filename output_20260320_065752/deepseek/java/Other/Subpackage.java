package subpackage;

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