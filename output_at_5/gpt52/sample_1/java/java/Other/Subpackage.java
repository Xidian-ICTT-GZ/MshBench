package subpackage;

interface Interface1
{
}

public class Subpackage implements Interface1
{
    //@ requires true;
    //@ ensures true;
    public Subpackage()
    {
    }
}