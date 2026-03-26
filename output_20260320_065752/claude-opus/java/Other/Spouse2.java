class Person {

    private Person spouse;

/*@
predicate person_inv(Person this) = this != null &*&
    (this.spouse == null || this.spouse.spouse == this);
@*/

    protected Person getSpouse0()
        //@ requires person_inv(this);
        //@ ensures person_inv(this) &*& result == this.spouse;
    {
        Person result = spouse;
        return result;
    }

    protected void setSpouse0(Person other)
        //@ requires person_inv(this) &*& other == null || person_inv(other);
        //@ ensures person_inv(this);
    {
        spouse = other;
    }

    protected void clearSpouse0()
        //@ requires person_inv(this);
        //@ ensures person_inv(this);
    {
        spouse = null;
    }

    protected void setSpouse(Person other)
        //@ requires person_inv(this) &*& other == null || person_inv(other);
        //@ ensures person_inv(this);
    {
        setSpouse0(other);
    }

    protected void clearSpouse()
        //@ requires person_inv(this);
        //@ ensures person_inv(this);
    {
        clearSpouse0();
    }

    protected void ticketLemma()
        //@ requires person_inv(this);
        //@ ensures person_inv(this);
    {
    }

    public void symmetryLemma()
        //@ requires person_inv(this);
        //@ ensures person_inv(this);
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    protected Person()
        //@ requires true;
        //@ ensures person_inv(this);
    {
    }

    public static Person create()
        //@ requires true;
        //@ ensures person_inv(result);
    {
        Person p = new Person();
        return p;
    }

    public Person getSpouse()
        //@ requires person_inv(this);
        //@ ensures person_inv(this);
    {
        return getSpouse0();
    }

    void marry(Person other)
        //@ requires person_inv(this) &*& person_inv(other);
        //@ ensures person_inv(this) &*& person_inv(other);
    {
        setSpouse0(other);
        other.setSpouse(this);
    }

    void divorce()
        //@ requires person_inv(this);
        //@ ensures person_inv(this);
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