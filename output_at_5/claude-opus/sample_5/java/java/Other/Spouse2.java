class Person {
    private Person spouse;
    /*@
    predicate person() = this.spouse |-> _;
    @*/

    protected Person getSpouse0()
        //@ requires person();
        //@ ensures person() &*& result == spouse;
    {
        Person result = spouse;
        return result;
    }

    protected void setSpouse0(Person other)
        //@ requires person();
        //@ ensures person();
    {
        //@ open person();
        spouse = other;
        //@ close person();
    }

    protected void clearSpouse0()
        //@ requires person();
        //@ ensures person();
    {
        //@ open person();
        spouse = null;
        //@ close person();
    }

    protected void setSpouse(Person other)
        //@ requires person();
        //@ ensures person();
    {
        setSpouse0(other);
    }

    protected void clearSpouse()
        //@ requires person();
        //@ ensures person();
    {
        clearSpouse0();
    }

    protected void ticketLemma()
        //@ requires true;
        //@ ensures true;
    {
    }

    public void symmetryLemma()
        //@ requires person();
        //@ ensures person();
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    protected Person()
        //@ requires true;
        //@ ensures person();
    {
        //@ close person();
    }

    public static Person create()
        //@ requires true;
        //@ ensures result != null &*& result.person();
    {
        Person p = new Person();
        return p;
    }

    public Person getSpouse()
        //@ requires person();
        //@ ensures person() &*& (result == null || result.person());
    {
        return getSpouse0();
    }

    void marry(Person other)
        //@ requires person() &*& other.person();
        //@ ensures person() &*& other.person();
    {
        //@ open person();
        //@ open other.person();
        setSpouse0(other);
        other.setSpouse(this);
        //@ close other.person();
        //@ close person();
    }

    void divorce()
        //@ requires person();
        //@ ensures person();
    {
        //@ open person();
        Person spouse = getSpouse0();
        if (spouse != null) {
            //@ open spouse.person();
            spouse.clearSpouse();
            //@ close spouse.person();
        }
        clearSpouse0();
        //@ close person();
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