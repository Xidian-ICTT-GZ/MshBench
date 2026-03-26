/*@ predicate person(Person p; Person spouse) = p.spouse |-> spouse; @*/

class Person {

    private Person spouse;

    //@ requires this |-> ?s &*& person(this, s);
    //@ ensures result == s &*& person(this, s);
    protected Person getSpouse0()
    {
        Person result = spouse;
        return result;
    }
    
    //@ requires this |-> _ &*& person(this, _) &*& other |-> ?s2 &*& person(other, s2);
    //@ ensures this |-> other &*& person(this, other) &*& other |-> s2 &*& person(other, s2);
    protected void setSpouse0(Person other)
    {
        spouse = other;
    }
    
    //@ requires this |-> _ &*& person(this, _);
    //@ ensures this |-> null &*& person(this, null);
    protected void clearSpouse0()
    {
        spouse = null;
    }
    
    //@ requires this |-> _ &*& person(this, _) &*& other |-> ?s2 &*& person(other, s2);
    //@ ensures this |-> other &*& person(this, other) &*& other |-> s2 &*& person(other, s2);
    protected void setSpouse(Person other)
    {
        setSpouse0(other);
    }
    
    //@ requires this |-> _ &*& person(this, _);
    //@ ensures this |-> null &*& person(this, null);
    protected void clearSpouse()
    {
        clearSpouse0();
    }
    
    //@ requires true;
    protected void ticketLemma()
    {
    }
    
    //@ requires this |-> ?s &*& person(this, s) &*& s != null &*& s |-> ?s2 &*& person(s, s2);
    //@ ensures this |-> s &*& person(this, s) &*& s |-> s2 &*& person(s, s2);
    public void symmetryLemma()
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    //@ ensures this |-> null &*& person(this, null);
    protected Person()
    {
    }
    
    //@ ensures result |-> null &*& person(result, null);
    public static Person create()
    {
        Person p = new Person();
        return p;
    }
    
    //@ requires this |-> ?s &*& person(this, s);
    //@ ensures result == s &*& person(this, s);
    public Person getSpouse()
    {
        return getSpouse0();
    }
    
    //@ requires this |-> _ &*& person(this, _) &*& other |-> _ &*& person(other, _) &*& this != other;
    //@ ensures this |-> other &*& person(this, other) &*& other |-> this &*& person(other, this);
    void marry(Person other)
    {
        setSpouse0(other);
        other.setSpouse(this);
    }
    
    //@ requires this |-> ?s &*& person(this, s) &*& s != null &*& s |-> this &*& person(s, this);
    //@ ensures this |-> null &*& person(this, null) &*& s |-> null &*& person(s, null);
    void divorce()
    {
        Person spouse = getSpouse0();
        spouse.clearSpouse();
        clearSpouse0();
    }

}

class Program {

    //@ requires true;
    //@ ensures true;
    public static void main(String[] args)
    {
        Person a = Person.create();
        Person b = Person.create();
        a.marry(b);
        b.divorce();
    }

}