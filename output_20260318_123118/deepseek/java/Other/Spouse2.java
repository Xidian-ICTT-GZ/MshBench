class Person {

    private Person spouse;

    //@ predicate valid() = spouse == null ? emp() : spouse.spouse |-> this;
    //@ predicate spouse(Person s) = spouse |-> s;

    protected Person getSpouse0()
        //@ requires valid();
        //@ ensures valid() &*& result == null ? emp() : result.spouse |-> this;
    {
        Person result = spouse;
        return result;
    }
    
    protected void setSpouse0(Person other)
        //@ requires valid() &*& other.valid();
        //@ ensures other.spouse(this) &*& spouse(other);
    {
        spouse = other;
    }
    
    protected void clearSpouse0()
        //@ requires spouse(?s) &*& s != null ? s.spouse(this) : emp();
        //@ ensures valid();
    {
        spouse = null;
    }
    
    protected void setSpouse(Person other)
        //@ requires valid() &*& other.valid();
        //@ ensures other.spouse(this) &*& spouse(other);
    {
        setSpouse0(other);
    }
    
    protected void clearSpouse()
        //@ requires spouse(?s) &*& s != null ? s.spouse(this) : emp();
        //@ ensures valid();
    {
        clearSpouse0();
    }
    
    protected void ticketLemma()
        //@ requires valid();
        //@ ensures valid();
    {
    }
    
    public void symmetryLemma()
        //@ requires valid();
        //@ ensures valid();
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    protected Person()
        //@ ensures valid();
    {
        spouse = null;
    }
    
    public static Person create()
        //@ ensures result.valid();
    {
        Person p = new Person();
        return p;
    }
    
    public Person getSpouse()
        //@ requires valid();
        //@ ensures valid() &*& result == null ? emp() : result.spouse |-> this;
    {
        return getSpouse0();
    }
    
    void marry(Person other)
        //@ requires valid() &*& other.valid();
        //@ ensures spouse(other) &*& other.spouse(this);
    {
        setSpouse0(other);
        other.setSpouse(this);
    }
    
    void divorce()
        //@ requires spouse(?s) &*& s != null ? s.spouse(this) : emp();
        //@ ensures valid() &*& s.valid();
    {
        Person spouse = getSpouse0();
        spouse.clearSpouse();
        clearSpouse0();
    }

}

class Program {

    public static void main(String[] args)
        //@ requires emp();
        //@ ensures emp();
    {
        Person a = Person.create();
        Person b = Person.create();
        a.marry(b);
        b.divorce();
    }

}