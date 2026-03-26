class Person {

    private Person spouse;

    /*@
    predicate person(Person spouse) = true;
    @*/

    protected Person getSpouse0()
    //@ requires this.person(?s);
    //@ ensures this.person(s) &*& result == s;
    {
        
        Person result = spouse;
        
        return result;
    }
    
    protected void setSpouse0(Person other)
    //@ requires this.person(?s);
    //@ ensures this.person(other);
    {
        
        spouse = other;
        
        
    }
    
    protected void clearSpouse0()
    //@ requires this.person(?s);
    //@ ensures this.person(null);
    {
        
        
        spouse = null;
        
    }
    
    protected void setSpouse(Person other)
    //@ requires this.person(?s) &*& other.person(?t);
    //@ ensures this.person(other) &*& other.person(this);
    {
        
        setSpouse0(other);
        
    }
    
    protected void clearSpouse()
    //@ requires this.person(?s);
    //@ ensures this.person(null);
    {
        
        clearSpouse0();
        
    }
    
    

    
    protected  void ticketLemma()
    //@ requires this.person(?s);
    //@ ensures this.person(s);
    {
        
        
        
    }
    
    public  void symmetryLemma()
    //@ requires this.person(?s) &*& s != null &*& s.person(this);
    //@ ensures this.person(s) &*& s.person(this);
    {
        
        Person spouse = getSpouse0();
        spouse.ticketLemma();
        
    }

    protected Person()
    //@ ensures this.person(null);
    {
        
    }
    
    

    
    public static Person create()
    //@ ensures result.person(null);
    {
        Person p = new Person();
        
        return p;
    }
    
    public Person getSpouse()
    //@ requires this.person(?s);
    //@ ensures this.person(s) &*& result == s;
    {
        
        return getSpouse0();
        
    }
    
    void marry(Person other)
    //@ requires this.person(null) &*& other.person(null);
    //@ ensures this.person(other) &*& other.person(this);
    {
        
        setSpouse0(other);
        other.setSpouse(this);
        
    }
    
    void divorce()
    //@ requires this.person(?s) &*& s != null &*& s.person(this);
    //@ ensures this.person(null) &*& s.person(null);
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