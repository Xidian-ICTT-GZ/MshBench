class Person {

    private Person spouse;

    /*@ predicate person(Person p; Person s) =
          this == p &*&
          this.spouse |-> s
    ;@*/

    //@ requires true;
    //@ ensures person(this, spouse);
    protected Person getSpouse0()
    {
        Person result = spouse;
        return result;
    }

    //@ requires person(this, _);
    //@ ensures person(this, other);
    protected void setSpouse0(Person other)
    {
        spouse = other;
    }

    //@ requires person(this, _);
    //@ ensures person(this, null);
    protected void clearSpouse0()
    {
        spouse = null;
    }

    //@ requires person(this, _);
    //@ ensures person(this, other);
    protected void setSpouse(Person other)
    {
        setSpouse0(other);
    }

    //@ requires person(this, _);
    //@ ensures person(this, null);
    protected void clearSpouse()
    {
        clearSpouse0();
    }

    //@ requires person(this, ?s);
    //@ ensures person(this, s);
    protected void ticketLemma()
    {
    }

    //@ requires person(this, ?s) &*& s != null &*& person(s, this);
    //@ ensures person(this, s) &*& person(s, this);
    public void symmetryLemma()
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    //@ requires true;
    //@ ensures person(this, null);
    protected Person()
    {
    }

    //@ requires true;
    //@ ensures person(result, null);
    public static Person create()
    {
        Person p = new Person();
        return p;
    }

    //@ requires person(this, ?s);
    //@ ensures person(this, s) &*& result == s;
    public Person getSpouse()
    {
        return getSpouse0();
    }

    //@ requires person(this, null) &*& person(other, null);
    //@ ensures person(this, other) &*& person(other, this);
    void marry(Person other)
    {
        setSpouse0(other);
        other.setSpouse(this);
    }

    //@ requires person(this, ?s) &*& s != null &*& person(s, this);
    //@ ensures person(this, null) &*& person(s, null);
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