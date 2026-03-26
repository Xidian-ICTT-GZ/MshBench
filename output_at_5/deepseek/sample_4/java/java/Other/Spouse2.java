/*@
predicate Person(Person p) = p.spouse |-> ?s;
@*/

class Person {

    private Person spouse;

    //@ requires Person(this);
    //@ ensures Person(this) &*& result == null;
    protected Person getSpouse0()
    {
        //@ open Person(this);
        Person result = spouse;
        //@ close Person(this);
        return result;
    }
    
    //@ requires Person(this);
    //@ ensures Person(this);
    protected void setSpouse0(Person other)
    {
        //@ open Person(this);
        spouse = other;
        //@ close Person(this);
    }
    
    //@ requires Person(this);
    //@ ensures Person(this);
    protected void clearSpouse0()
    {
        //@ open Person(this);
        spouse = null;
        //@ close Person(this);
    }
    
    //@ requires Person(this);
    //@ ensures Person(this);
    protected void setSpouse(Person other)
    {
        setSpouse0(other);
    }
    
    //@ requires Person(this);
    //@ ensures Person(this);
    protected void clearSpouse()
    {
        clearSpouse0();
    }
    
    //@ requires Person(this);
    //@ ensures Person(this);
    protected  void ticketLemma()
    {
    }
    
    //@ requires Person(this);
    //@ ensures Person(this);
    public  void symmetryLemma()
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    //@ ensures Person(this);
    protected Person()
    {
        //@ close Person(this);
    }
    
    //@ ensures Person(result);
    public static Person create()
    {
        Person p = new Person();
        return p;
    }
    
    //@ requires Person(this);
    //@ ensures Person(this) &*& result == null;
    public Person getSpouse()
    {
        return getSpouse0();
    }
    
    //@ requires Person(this) &*& Person(other);
    //@ ensures Person(this) &*& Person(other);
    void marry(Person other)
    {
        setSpouse0(other);
        other.setSpouse(this);
    }
    
    //@ requires Person(this);
    //@ ensures Person(this);
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