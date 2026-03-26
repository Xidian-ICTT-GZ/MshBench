class Person {

    private Person spouse;

    /*@ predicate person_spouse(Person p, Person s) =
          this == p &*& spouse |-> s; @*/

    //@ requires person_spouse(this, ?s);
    //@ ensures person_spouse(this, s);
    protected Person getSpouse0()
    {
        Person result = spouse;
        return result;
    }
    
    //@ requires person_spouse(this, ?s);
    //@ ensures person_spouse(this, other);
    protected void setSpouse0(Person other)
    {
        spouse = other;
    }
    
    //@ requires person_spouse(this, ?s);
    //@ ensures person_spouse(this, null);
    protected void clearSpouse0()
    {
        spouse = null;
    }
    
    //@ requires person_spouse(this, ?s);
    //@ ensures person_spouse(this, other);
    protected void setSpouse(Person other)
    {
        setSpouse0(other);
    }
    
    //@ requires person_spouse(this, ?s);
    //@ ensures person_spouse(this, null);
    protected void clearSpouse()
    {
        clearSpouse0();
    }
    
    //@ requires person_spouse(this, ?s);
    //@ ensures person_spouse(this, s) &*& s.person_spouse(s, this);
    protected  void ticketLemma()
    {
    }
    
    //@ requires person_spouse(this, ?spouse) &*& spouse != null &*& person_spouse(spouse, ?s);
    //@ ensures  person_spouse(this, spouse) &*& person_spouse(spouse, this);
    public  void symmetryLemma()
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    //@ requires true;
    //@ ensures person_spouse(this, null);
    protected Person()
    {
    }
    
    //@ requires true;
    //@ ensures person_spouse(result, null);
    public static Person create()
    {
        Person p = new Person();
        return p;
    }
    
    //@ requires person_spouse(this, ?s);
    //@ ensures person_spouse(this, s);
    public Person getSpouse()
    {
        return getSpouse0();
    }
    
    //@ requires person_spouse(this, null) &*& person_spouse(other, null);
    //@ ensures person_spouse(this, other) &*& person_spouse(other, this);
    void marry(Person other)
    {
        setSpouse0(other);
        other.setSpouse(this);
    }
    
    //@ requires person_spouse(this, ?s) &*& s != null &*& person_spouse(s, this);
    //@ ensures person_spouse(this, null) &*& person_spouse(s, null);
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