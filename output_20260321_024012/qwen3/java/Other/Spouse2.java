/*@ predicate Person_spouse(Person p; Person spouse) = p.spouse |-> spouse; @*/

class Person {

    private Person spouse;

    
    //@ requires this |-> ?s &*& Person_spouse(this, s);
    //@ ensures this |-> s &*& Person_spouse(this, s) &*& result == s;
    protected Person getSpouse0()
    {
        Person result = spouse;
        return result;
    }
    
    //@ requires this |-> _ &*& Person_spouse(this, _) &*& other |-> ?s2 &*& Person_spouse(other, s2);
    //@ ensures this |-> other &*& Person_spouse(this, other) &*& other |-> s2 &*& Person_spouse(other, s2);
    protected void setSpouse0(Person other)
    {
        spouse = other;
    }
    
    //@ requires this |-> _ &*& Person_spouse(this, _);
    //@ ensures this |-> null &*& Person_spouse(this, null);
    protected void clearSpouse0()
    {
        spouse = null;
    }
    
    //@ requires this |-> _ &*& Person_spouse(this, _) &*& other |-> ?s2 &*& Person_spouse(other, s2);
    //@ ensures this |-> other &*& Person_spouse(this, other) &*& other |-> s2 &*& Person_spouse(other, s2);
    protected void setSpouse(Person other)
    {
        setSpouse0(other);
    }
    
    //@ requires this |-> _ &*& Person_spouse(this, _);
    //@ ensures this |-> null &*& Person_spouse(this, null);
    protected void clearSpouse()
    {
        clearSpouse0();
    }
    
    //@ requires true;
    //@ ensures true;
    protected  void ticketLemma()
    {
    }
    
    //@ requires this |-> ?s &*& Person_spouse(this, s) &*& s != null &*& s |-> ?s2 &*& Person_spouse(s, s2);
    //@ ensures this |-> s &*& Person_spouse(this, s) &*& s |-> s2 &*& Person_spouse(s, s2);
    public  void symmetryLemma()
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    protected Person()
    {
        //@ close Person_spouse(this, null);
    }
    
    //@ ensures result |-> null &*& Person_spouse(result, null);
    public static Person create()
    {
        Person p = new Person();
        return p;
    }
    
    //@ requires this |-> ?s &*& Person_spouse(this, s);
    //@ ensures this |-> s &*& Person_spouse(this, s) &*& result == s;
    public Person getSpouse()
    {
        return getSpouse0();
    }
    
    //@ requires this |-> _ &*& Person_spouse(this, _) &*& other |-> _ &*& Person_spouse(other, _) &*& this != other;
    //@ ensures this |-> other &*& Person_spouse(this, other) &*& other |-> this &*& Person_spouse(other, this);
    void marry(Person other)
    {
        setSpouse0(other);
        other.setSpouse(this);
    }
    
    //@ requires this |-> ?s &*& Person_spouse(this, s) &*& s != null &*& s |-> this &*& Person_spouse(s, this);
    //@ ensures this |-> null &*& Person_spouse(this, null) &*& s |-> null &*& Person_spouse(s, null);
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