class Person {

    private Person spouse;
    //@ predicate Person() = spouse |-> ?s &*& (s == null ? true : s.spouse |-> this);

    //@ requires true;
    //@ ensures Person();
    protected Person()
    {
        //@ close Person();
    }

    //@ requires Person();
    //@ ensures Person() &*& result == spouse;
    protected Person getSpouse0()
    {
        //@ open Person();
        Person result = spouse;
        //@ close Person();
        return result;
    }

    //@ requires Person() &*& other != null;
    //@ ensures Person();
    protected void setSpouse0(Person other)
    {
        //@ open Person();
        spouse = other;
        //@ close Person();
    }

    //@ requires Person();
    //@ ensures Person();
    protected void clearSpouse0()
    {
        //@ open Person();
        spouse = null;
        //@ close Person();
    }

    //@ requires Person() &*& other != null;
    //@ ensures Person();
    protected void setSpouse(Person other)
    {
        setSpouse0(other);
    }

    //@ requires Person();
    //@ ensures Person();
    protected void clearSpouse()
    {
        clearSpouse0();
    }

    //@ requires Person();
    //@ ensures Person();
    protected void ticketLemma()
    {
    }

    //@ requires Person();
    //@ ensures Person();
    public void symmetryLemma()
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    //@ requires true;
    //@ ensures Person();
    public static Person create()
    {
        Person p = new Person();
        return p;
    }

    //@ requires Person();
    //@ ensures Person() &*& result == spouse;
    public Person getSpouse()
    {
        return getSpouse0();
    }

    //@ requires Person() &*& other != null &*& other.Person();
    //@ ensures Person() &*& other.Person();
    void marry(Person other)
    {
        setSpouse0(other);
        other.setSpouse(this);
    }

    //@ requires Person() &*& spouse != null &*& spouse.Person();
    //@ ensures Person() &*& spouse.Person();
    void divorce()
    {
        Person spouse = getSpouse0();
        spouse.clearSpouse();
        clearSpouse0();
    }

}

class Program {

    public static void main(String[] args)
    {
        Person a = Person.create();
        Person b = Person.create();
        a.marry(b);
        b.divorce();
    }

}