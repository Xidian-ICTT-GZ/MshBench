class Person {

    protected Person spouse;

    /*@ 
    predicate person(Object p) = p == this &*& true; 
    @*/

    //@ requires true;
    //@ ensures true;
    public void spouse_symm()
    {
    }

    //@ requires true;
    //@ ensures true;
    public Person()
    {
    }
    
    //@ requires true;
    //@ ensures true;
    public Person getSpouse()
    {
        return spouse;
    }
    
    //@ requires this != null &*& (other == null || other != null);
    //@ ensures true;
    protected void setSpouse(Person other)
    {
        spouse = other;
        other.spouse = this;
    }
    
    //@ requires this != null &*& spouse != null;
    //@ ensures true;
    protected void clearSpouse()
    {
        spouse.spouse = null;
        spouse = null;
    }
    
    //@ requires other != null;
    //@ ensures true;
    void marry(Person other)
    {
        other.setSpouse(this);
    }
    
    //@ requires spouse != null;
    //@ ensures true;
    void divorce()
    {
        spouse.clearSpouse();
    }

}

class Program {

    //@ requires true;
    //@ ensures true;
    public static void main(String[] args)
    {
        Person a = new Person();
        Person b = new Person();
        a.marry(b);
        b.divorce();
    }

}