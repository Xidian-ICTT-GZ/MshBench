package subpackage;

interface Interface1
{
    //@ public normal_behavior
    //@ ensures true;
    void dummy();
}

public class Subpackage implements Interface1
{
    //@ public normal_behavior
    //@ ensures true;
    public void dummy() {}
}