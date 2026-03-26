class Person {

    private Person spouse;

    /*@
    predicate person(Person s) = this.spouse |-> s;
    @*/

    protected Person getSpouse0()
    //@ requires person(?s);
    //@ ensures person(s) &*& result == s;
    {
        Person result = spouse;
        return result;
    }

    protected void setSpouse0(Person other)
    //@ requires person(_);
    //@ ensures person(other);
    {
        spouse = other;
    }

    protected void clearSpouse0()
    //@ requires person(_);
    //@ ensures person(null);
    {
        spouse = null;
    }

    protected void setSpouse(Person other)
    //@ requires person(_);
    //@ ensures person(other);
    {
        setSpouse0(other);
    }

    protected void clearSpouse()
    //@ requires person(_);
    //@ ensures person(null);
    {
        clearSpouse0();
    }

    protected void ticketLemma()
    //@ requires person(_);
    //@ ensures person(_);
    {
    }

    public void symmetryLemma()
    //@ requires person(?s) &*& s != null &*& s.person(_);
    //@ ensures person(s) &*& s.person(_);
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    protected Person()
    //@ requires true;
    //@ ensures person(null);
    {
        //@ close person(null);
    }

    public static Person create()
    //@ requires true;
    //@ ensures result != null &*& result.person(null);
    {
        Person p = new Person();
        return p;
    }

    public Person getSpouse()
    //@ requires person(?s);
    //@ ensures person(s) &*& result == s;
    {
        return getSpouse0();
    }

    void marry(Person other)
    //@ requires person(_) &*& other != null &*& other.person(_);
    //@ ensures person(other) &*& other.person(this);
    {
        setSpouse0(other);
        other.setSpouse(this);
    }

    void divorce()
    //@ requires person(?s) &*& s != null &*& s.person(this);
    //@ ensures person(null) &*& s.person(null);
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