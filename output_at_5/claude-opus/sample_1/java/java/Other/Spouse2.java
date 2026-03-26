class Person {
    private Person spouse;
    /*@
    predicate person(this) = this.spouse |-> ?s;
    @*/

    protected Person getSpouse0()
        //@ requires person(this);
        //@ ensures person(this) &*& result == spouse;
    {
        Person result = spouse;
        return result;
    }

    protected void setSpouse0(Person other)
        //@ requires person(this);
        //@ ensures person(this);
    {
        //@ open person(this);
        spouse = other;
        //@ close person(this);
    }

    protected void clearSpouse0()
        //@ requires person(this);
        //@ ensures person(this);
    {
        //@ open person(this);
        spouse = null;
        //@ close person(this);
    }

    protected void setSpouse(Person other)
        //@ requires person(this);
        //@ ensures person(this);
    {
        setSpouse0(other);
    }

    protected void clearSpouse()
        //@ requires person(this);
        //@ ensures person(this);
    {
        clearSpouse0();
    }

    protected void ticketLemma()
        //@ requires true;
        //@ ensures true;
    {
    }

    public void symmetryLemma()
        //@ requires person(this);
        //@ ensures person(this);
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    protected Person()
        //@ requires true;
        //@ ensures person(this);
    {
        //@ close person(this);
    }

    public static Person create()
        //@ requires true;
        //@ ensures person(result);
    {
        Person p = new Person();
        return p;
    }

    public Person getSpouse()
        //@ requires person(this);
        //@ ensures person(this) &*& person(result) &*& result == spouse;
    {
        return getSpouse0();
    }

    void marry(Person other)
        //@ requires person(this) &*& person(other);
        //@ ensures person(this) &*& person(other);
    {
        //@ open person(this);
        //@ open person(other);
        setSpouse0(other);
        other.setSpouse(this);
        //@ close person(this);
        //@ close person(other);
    }

    void divorce()
        //@ requires person(this);
        //@ ensures person(this);
    {
        //@ open person(this);
        Person spouse = getSpouse0();
        //@ open person(spouse);
        spouse.clearSpouse();
        //@ close person(spouse);
        clearSpouse0();
        //@ close person(this);
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