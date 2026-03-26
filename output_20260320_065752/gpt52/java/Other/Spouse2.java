class Person {

    private Person spouse;

    /*@
    predicate PersonState(Person p; Person s) =
        p.spouse |-> s;
    @*/

    protected Person getSpouse0()
    //@ requires PersonState(this, ?s);
    //@ ensures PersonState(this, s) &*& result == s;
    {
        //@ open PersonState(this, s);
        Person result = spouse;
        //@ close PersonState(this, s);
        return result;
    }
    
    protected void setSpouse0(Person other)
    //@ requires PersonState(this, _);
    //@ ensures PersonState(this, other);
    {
        //@ open PersonState(this, _);
        spouse = other;
        //@ close PersonState(this, other);
    }
    
    protected void clearSpouse0()
    //@ requires PersonState(this, _);
    //@ ensures PersonState(this, null);
    {
        //@ open PersonState(this, _);
        spouse = null;
        //@ close PersonState(this, null);
    }
    
    protected void setSpouse(Person other)
    //@ requires PersonState(this, _);
    //@ ensures PersonState(this, other);
    {
        setSpouse0(other);
    }
    
    protected void clearSpouse()
    //@ requires PersonState(this, _);
    //@ ensures PersonState(this, null);
    {
        clearSpouse0();
    }
    
    protected  void ticketLemma()
    //@ requires true;
    //@ ensures true;
    {
    }
    
    public  void symmetryLemma()
    //@ requires PersonState(this, ?s) &*& s != null;
    //@ ensures PersonState(this, s);
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    protected Person()
    //@ requires true;
    //@ ensures PersonState(this, null);
    {
        //@ close PersonState(this, null);
    }
    
    public static Person create()
    //@ requires true;
    //@ ensures PersonState(result, null);
    {
        Person p = new Person();
        return p;
    }
    
    public Person getSpouse()
    //@ requires PersonState(this, ?s);
    //@ ensures PersonState(this, s) &*& result == s;
    {
        return getSpouse0();
    }
    
    void marry(Person other)
    //@ requires PersonState(this, _) &*& PersonState(other, _);
    //@ ensures PersonState(this, other) &*& PersonState(other, this);
    {
        setSpouse0(other);
        other.setSpouse(this);
    }
    
    void divorce()
    //@ requires PersonState(this, ?s) &*& PersonState(s, this);
    //@ ensures PersonState(this, null) &*& PersonState(s, null);
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
        //@ open Person.PersonState(a, _);
        //@ open Person.PersonState(b, _);
    }

}