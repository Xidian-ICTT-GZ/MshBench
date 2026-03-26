/*@
predicate Person(Person p;) = p.spouse |-> ?s &*& (s == null ? true : Person(s));
@*/

class Person {

    private Person spouse;

    /*@
    predicate valid() = Person(this);
    @*/

    //@ requires true;
    //@ ensures valid();
    protected Person()
    {
        //@ close valid();
    }
    
    //@ requires valid();
    //@ ensures valid() &*& result == spouse;
    protected Person getSpouse0()
    {
        //@ open valid();
        Person result = spouse;
        //@ close valid();
        return result;
    }
    
    //@ requires valid() &*& other == null ? true : Person(other);
    //@ ensures valid();
    protected void setSpouse0(Person other)
    {
        //@ open valid();
        spouse = other;
        //@ close valid();
    }
    
    //@ requires valid();
    //@ ensures valid();
    protected void clearSpouse0()
    {
        //@ open valid();
        spouse = null;
        //@ close valid();
    }
    
    //@ requires valid() &*& other == null ? true : Person(other);
    //@ ensures valid();
    protected void setSpouse(Person other)
    {
        setSpouse0(other);
    }
    
    //@ requires valid();
    //@ ensures valid();
    protected void clearSpouse()
    {
        clearSpouse0();
    }
    
    //@ requires valid();
    //@ ensures valid();
    protected void ticketLemma()
    {
    }
    
    //@ requires valid();
    //@ ensures valid();
    public void symmetryLemma()
    {
        Person spouse = getSpouse0();
        if (spouse != null) {
            //@ assert Person(spouse);
            spouse.ticketLemma();
        }
    }

    //@ requires true;
    //@ ensures valid();
    public static Person create()
    {
        Person p = new Person();
        return p;
    }
    
    //@ requires valid();
    //@ ensures valid() &*& result == spouse;
    public Person getSpouse()
    {
        return getSpouse0();
    }
    
    //@ requires valid() &*& Person(other);
    //@ ensures valid() &*& Person(other);
    void marry(Person other)
    {
        //@ open Person(other);
        setSpouse0(other);
        other.setSpouse(this);
        //@ close Person(other);
    }
    
    //@ requires valid();
    //@ ensures valid();
    void divorce()
    {
        Person spouse = getSpouse0();
        if (spouse != null) {
            //@ assert Person(spouse);
            spouse.clearSpouse();
        }
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