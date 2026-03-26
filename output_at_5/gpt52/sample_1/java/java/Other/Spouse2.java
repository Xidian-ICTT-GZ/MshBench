class Person {

    private Person spouse;

    /*@
    predicate person(Person p; Person s) =
        p.spouse |-> s;
    @*/

    protected Person getSpouse0()
    //@ requires person(this, ?s);
    //@ ensures person(this, s) &*& result == s;
    {
        //@ open person(this, s);
        Person result = spouse;
        //@ close person(this, s);
        return result;
    }
    
    protected void setSpouse0(Person other)
    //@ requires person(this, ?s0);
    //@ ensures person(this, other);
    {
        //@ open person(this, s0);
        spouse = other;
        //@ close person(this, other);
    }
    
    protected void clearSpouse0()
    //@ requires person(this, ?s0);
    //@ ensures person(this, null);
    {
        //@ open person(this, s0);
        spouse = null;
        //@ close person(this, null);
    }
    
    protected void setSpouse(Person other)
    //@ requires person(this, ?s0);
    //@ ensures person(this, other);
    {
        setSpouse0(other);
    }
    
    protected void clearSpouse()
    //@ requires person(this, ?s0);
    //@ ensures person(this, null);
    {
        clearSpouse0();
    }
    
    protected  void ticketLemma()
    //@ requires true;
    //@ ensures true;
    {
    }
    
    public  void symmetryLemma()
    //@ requires person(this, ?s) &*& s != null;
    //@ ensures person(this, s);
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    protected Person()
    //@ requires true;
    //@ ensures person(this, null);
    {
        //@ close person(this, null);
    }
    
    public static Person create()
    //@ requires true;
    //@ ensures person(result, null);
    {
        Person p = new Person();
        return p;
    }
    
    public Person getSpouse()
    //@ requires person(this, ?s);
    //@ ensures person(this, s) &*& result == s;
    {
        return getSpouse0();
    }
    
    void marry(Person other)
    //@ requires person(this, ?s1) &*& person(other, ?s2);
    //@ ensures person(this, other) &*& person(other, this);
    {
        setSpouse0(other);
        other.setSpouse(this);
    }
    
    void divorce()
    //@ requires person(this, ?s) &*& s != null &*& person(s, ?ss);
    //@ ensures person(this, null) &*& person(s, null);
    {
        Person spouse = getSpouse0();
        spouse.clearSpouse();
        clearSpouse0();
    }

}

class Program {

    public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    {
        Person a = Person.create();
        Person b = Person.create();
        a.marry(b);
        b.divorce();
    }

}