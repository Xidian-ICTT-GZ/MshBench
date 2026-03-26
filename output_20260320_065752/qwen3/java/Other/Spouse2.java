class Person {

    private Person spouse;

    /*@
    predicate person(Person spouse) = true;
    @*/

    //@ requires this.person(?s);
    //@ ensures this.person(result);
    protected Person getSpouse0()
    {
        Person result = spouse;
        return result;
    }
    
    //@ requires this.person(?s) &*& other != null ? other.person(?t) : true;
    //@ ensures this.person(other);
    protected void setSpouse0(Person other)
    {
        spouse = other;
    }
    
    //@ requires this.person(?s);
    //@ ensures this.person(null);
    protected void clearSpouse0()
    {
        spouse = null;
    }
    
    //@ requires this.person(?s) &*& other != null ? other.person(?t) : true;
    //@ ensures this.person(other);
    protected void setSpouse(Person other)
    {
        setSpouse0(other);
    }
    
    //@ requires this.person(?s);
    //@ ensures this.person(null);
    protected void clearSpouse()
    {
        clearSpouse0();
    }
    
    //@ requires true;
    //@ ensures true;
    protected  void ticketLemma()
    {
    }
    
    //@ requires this.person(?s) &*& s != null ? s.person(?t) : true;
    //@ ensures true;
    public  void symmetryLemma()
    {
        Person spouse = getSpouse0();
        if (spouse != null) {
            spouse.ticketLemma();
        }
    }

    protected Person()
    {
        //@ close person(null);
    }
    
    //@ ensures result != null &*& result.person(null);
    public static Person create()
    {
        Person p = new Person();
        return p;
    }
    
    //@ requires this.person(?s);
    //@ ensures this.person(result);
    public Person getSpouse()
    {
        return getSpouse0();
    }
    
    //@ requires this.person(?s1) &*& other != null &*& other.person(?s2);
    //@ ensures this.person(other) &*& other.person(this);
    void marry(Person other)
    {
        setSpouse0(other);
        other.setSpouse(this);
    }
    
    //@ requires this.person(?s1) &*& s1 != null &*& s1.person(this);
    //@ ensures this.person(null) &*& s1.person(null);
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