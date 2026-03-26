class Person {

    private Person spouse;

    //@ predicate valid() = spouse == null ? emp() : spouse.spouse |-> this &*& spouse.valid();
    //@ predicate spouse(Person s) = spouse |-> s;

    protected Person getSpouse0()
        //@ requires valid();
        //@ ensures valid() &*& result == null ? emp() : result.spouse |-> this &*& result.valid();
    {
        Person result = spouse;
        return result;
    }
    
    protected void setSpouse0(Person other)
        //@ requires valid() &*& other.valid();
        //@ ensures spouse(other) &*& other.spouse(this);
    {
        spouse = other;
        //@ close spouse(other);
        //@ close other.spouse(this);
    }
    
    protected void clearSpouse0()
        //@ requires spouse(?s);
        //@ ensures valid();
    {
        spouse = null;
        //@ close valid();
    }
    
    protected void setSpouse(Person other)
        //@ requires valid() &*& other.valid();
        //@ ensures spouse(other) &*& other.spouse(this);
    {
        setSpouse0(other);
    }
    
    protected void clearSpouse()
        //@ requires spouse(?s);
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
        if (spouse != null) {
            spouse.ticketLemma();
        }
    }

    protected Person()
        //@ ensures valid();
    {
        spouse = null;
        //@ close valid();
    }
    
    public static Person create()
        //@ requires emp();
        //@ ensures result.valid();
    {
        Person p = new Person();
        return p;
    }
    
    public Person getSpouse()
        //@ requires valid();
        //@ ensures valid() &*& result == null ? emp() : result.spouse |-> this &*& result.valid();
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
        //@ requires spouse(?s) &*& s.spouse(this);
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