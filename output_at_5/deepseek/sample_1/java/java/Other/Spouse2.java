/*@
predicate Person(Person p) = p.spouse |-> ?s;
@*/

class Person {

    private Person spouse;

    //@ requires true;
    //@ ensures Person(this);
    //@ ensures result == null;
    protected Person getSpouse0()
    //@ requires Person(this);
    //@ ensures Person(this) &*& result == null;
    {
        Person result = spouse;
        return result;
    }
    
    //@ requires Person(this);
    //@ ensures Person(this);
    protected void setSpouse0(Person other)
    //@ requires Person(this);
    //@ ensures Person(this);
    {
        spouse = other;
    }
    
    //@ requires Person(this);
    //@ ensures Person(this);
    protected void clearSpouse0()
    //@ requires Person(this);
    //@ ensures Person(this);
    {
        spouse = null;
    }
    
    //@ requires Person(this);
    //@ ensures Person(this);
    protected void setSpouse(Person other)
    //@ requires Person(this);
    //@ ensures Person(this);
    {
        setSpouse0(other);
    }
    
    //@ requires Person(this);
    //@ ensures Person(this);
    protected void clearSpouse()
    //@ requires Person(this);
    //@ ensures Person(this);
    {
        clearSpouse0();
    }
    
    //@ requires Person(this);
    //@ ensures Person(this);
    protected void ticketLemma()
    //@ requires Person(this);
    //@ ensures Person(this);
    {
    }
    
    //@ requires Person(this);
    //@ ensures Person(this);
    public void symmetryLemma()
    //@ requires Person(this);
    //@ ensures Person(this);
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    //@ ensures Person(this);
    protected Person()
    //@ ensures Person(this);
    {
    }
    
    //@ ensures Person(result);
    public static Person create()
    //@ ensures Person(result);
    {
        Person p = new Person();
        return p;
    }
    
    //@ requires Person(this);
    //@ ensures Person(this) &*& result == null;
    public Person getSpouse()
    //@ requires Person(this);
    //@ ensures Person(this) &*& result == null;
    {
        return getSpouse0();
    }
    
    //@ requires Person(this) &*& Person(other);
    //@ ensures Person(this) &*& Person(other);
    void marry(Person other)
    //@ requires Person(this) &*& Person(other);
    //@ ensures Person(this) &*& Person(other);
    {
        setSpouse0(other);
        other.setSpouse(this);
    }
    
    //@ requires Person(this);
    //@ ensures Person(this);
    void divorce()
    //@ requires Person(this);
    //@ ensures Person(this);
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
    //@ requires true;
    //@ ensures true;
    {
        Person a = Person.create();
        Person b = Person.create();
        a.marry(b);
        b.divorce();
    }
}