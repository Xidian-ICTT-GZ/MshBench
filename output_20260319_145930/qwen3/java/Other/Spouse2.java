/*@ predicate spouse(Person p; Person s) = p.spouse |-> s; @*/

class Person {

    private Person spouse;

    //@ requires this.spouse |-> ?s;
    //@ ensures result == s;
    protected Person getSpouse0()
    {
        Person result = spouse;
        return result;
    }
    
    //@ requires this.spouse |-> _;
    //@ ensures this.spouse |-> other;
    protected void setSpouse0(Person other)
    {
        spouse = other;
    }
    
    //@ requires this.spouse |-> _;
    //@ ensures this.spouse |-> null;
    protected void clearSpouse0()
    {
        spouse = null;
    }
    
    //@ requires this.spouse |-> _;
    //@ ensures this.spouse |-> other;
    protected void setSpouse(Person other)
    {
        setSpouse0(other);
    }
    
    //@ requires this.spouse |-> _;
    //@ ensures this.spouse |-> null;
    protected void clearSpouse()
    {
        clearSpouse0();
    }
    
    //@ requires true;
    protected void ticketLemma()
    {
    }
    
    //@ requires this.spouse |-> ?s &*& s != null &*& s.spouse |-> _;
    public void symmetryLemma()
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    //@ ensures this.spouse |-> null;
    protected Person()
    {
    }
    
    //@ ensures result.spouse |-> null;
    public static Person create()
    {
        Person p = new Person();
        return p;
    }
    
    //@ requires this.spouse |-> ?s;
    //@ ensures result == s;
    public Person getSpouse()
    {
        return getSpouse0();
    }
    
    //@ requires this.spouse |-> _ &*& other.spouse |-> _;
    //@ ensures this.spouse |-> other &*& other.spouse |-> this;
    void marry(Person other)
    {
        setSpouse0(other);
        other.setSpouse(this);
    }
    
    //@ requires this.spouse |-> ?s &*& s != null &*& s.spouse |-> this;
    //@ ensures this.spouse |-> null &*& s.spouse |-> null;
    void divorce()
    {
        Person spouse = getSpouse0();
        spouse.clearSpouse();
        clearSpouse0();
    }

}

class Program {

    public static void main(String[] args)
    {
        Person a = Person.create();
        Person b = Person.create();
        a.marry(b);
        b.divorce();
    }

}