package subpackage;

interface Interface1
{
    //@ predicate interface1() = true;
}

public class Subpackage implements Interface1
{
    //@ predicate subpackage() = true;
    
    //@ requires true;
    //@ ensures subpackage();
    public Subpackage()
    {
        //@ close subpackage();
    }
}