class Person {

    private Person spouse;

    /*@
    predicate object(this) = this.spouse |-> ?s;
    @*/

    
    protected Person getSpouse0()
    //@ requires object(this);
    //@ ensures object(this) &*& result == spouse;
    {
        //@ open object(this);
        Person result = spouse;
        //@ close object(this);
        return result;
    }
    
    protected void setSpouse0(Person other)
    //@ requires object(this);
    //@ ensures object(this);
    {
        //@ open object(this);
        spouse = other;
        //@ close object(this);
    }
    
    protected void clearSpouse0()
    //@ requires object(this);
    //@ ensures object(this);
    {
        //@ open object(this);
        spouse = null;
        //@ close object(this);
    }
    
    protected void setSpouse(Person other)
    //@ requires object(this);
    //@ ensures object(this);
    {
        setSpouse0(other);
    }
    
    protected void clearSpouse()
    //@ requires object(this);
    //@ ensures object(this);
    {
        clearSpouse0();
    }
    
    
    protected void ticketLemma()
    //@ requires object(this);
    //@ ensures object(this);
    {
    }
    
    public void symmetryLemma()
    //@ requires object(this);
    //@ ensures object(this);
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    protected Person()
    //@ requires true;
    //@ ensures object(this);
    {
        //@ close object(this);
    }
    
    
    public static Person create()
    //@ requires true;
    //@ ensures object(result);
    {
        Person p = new Person();
        return p;
    }
    
    public Person getSpouse()
    //@ requires object(this);
    //@ ensures object(this) &*& result == spouse;
    {
        return getSpouse0();
    }
    
    void marry(Person other)
    //@ requires object(this) &*& object(other);
    //@ ensures object(this) &*& object(other) &*& spouse == other;
    {
        //@ open object(this);
        setSpouse0(other);
        //@ close object(this);
        //@ open object(other);
        other.setSpouse(this);
        //@ close object(other);
    }
    
    void divorce()
    //@ requires object(this);
    //@ ensures object(this) &*& spouse == null;
    {
        //@ open object(this);
        Person spouse = getSpouse0();
        //@ close object(this);
        spouse.clearSpouse();
        //@ open object(this);
        clearSpouse0();
        //@ close object(this);
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