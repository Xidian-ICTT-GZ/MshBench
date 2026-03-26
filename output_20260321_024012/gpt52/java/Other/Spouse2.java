class Person {

    private Person spouse;

    /*@
    predicate person(Person p; Person s) =
        p.spouse |-> s;
    @*/

    
    //@ requires person(this, ?s);
    //@ ensures person(this, s) &*& result == s;
    protected Person getSpouse0()
        
        
    {
        //@ open person(this, ?s0);
        Person result = spouse;
        //@ close person(this, s0);
        return result;
    }
    
    //@ requires person(this, ?s);
    //@ ensures person(this, other);
    protected void setSpouse0(Person other)
        
        
    {
        //@ open person(this, ?s0);
        spouse = other;
        //@ close person(this, other);
        
        
    }
    
    //@ requires person(this, ?s);
    //@ ensures person(this, null);
    protected void clearSpouse0()
        
        
    {
        
        
        //@ open person(this, ?s0);
        spouse = null;
        //@ close person(this, null);
        
    }
    
    //@ requires person(this, ?s);
    //@ ensures person(this, other);
    protected void setSpouse(Person other)
        
        
    {
        
        setSpouse0(other);
        
    }
    
    //@ requires person(this, ?s);
    //@ ensures person(this, null);
    protected void clearSpouse()
        
        
    {
        
        clearSpouse0();
        
    }
    
    
    //@ requires true;
    //@ ensures true;
    protected  void ticketLemma()
        
        
    {
        
        
        
    }
    
    //@ requires person(this, ?s) &*& s != null &*& person(s, ?ss);
    //@ ensures person(this, s) &*& person(s, ss);
    public  void symmetryLemma()
        
        
    {
        
        Person spouse = getSpouse0();
        spouse.ticketLemma();
        
    }

    //@ requires true;
    //@ ensures person(this, null);
    protected Person()
        
        
    {
        //@ close person(this, null);
    }
    
    
    //@ requires true;
    //@ ensures person(result, null);
    public static Person create()
        
        
    {
        Person p = new Person();
        
        return p;
    }
    
    //@ requires person(this, ?s);
    //@ ensures person(this, s) &*& result == s;
    public Person getSpouse()
        
        
    {
        
        return getSpouse0();
        
    }
    
    //@ requires person(this, ?s1) &*& person(other, ?s2);
    //@ ensures person(this, other) &*& person(other, this);
    void marry(Person other)
        
        
    {
        
        setSpouse0(other);
        other.setSpouse(this);
        
    }
    
    //@ requires person(this, ?s) &*& s != null &*& person(s, ?ss);
    //@ ensures person(this, null) &*& person(s, null);
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