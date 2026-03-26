/*@
predicate Person_spouse(Person p; Person s) = p.spouse |-> s;

predicate Person(Person p;) = p.spouse |-> ?s;

predicate MarriedPair(Person p1, Person p2;) =
    p1.spouse |-> p2 &*& p2.spouse |-> p1 &*& p1 != null &*& p2 != null;

predicate Single(Person p;) = p.spouse |-> null &*& p != null;
@*/

class Person {

    private Person spouse;

    protected Person getSpouse0()
        //@ requires Person_spouse(this, ?s);
        //@ ensures Person_spouse(this, s) &*& result == s;
    {
        //@ open Person_spouse(this, s);
        Person result = spouse;
        //@ close Person_spouse(this, s);
        return result;
    }
    
    protected void setSpouse0(Person other)
        //@ requires Person_spouse(this, _);
        //@ ensures Person_spouse(this, other);
    {
        //@ open Person_spouse(this, _);
        spouse = other;
        //@ close Person_spouse(this, other);
    }
    
    protected void clearSpouse0()
        //@ requires Person_spouse(this, _);
        //@ ensures Person_spouse(this, null);
    {
        //@ open Person_spouse(this, _);
        spouse = null;
        //@ close Person_spouse(this, null);
    }
    
    protected void setSpouse(Person other)
        //@ requires Person_spouse(this, _);
        //@ ensures Person_spouse(this, other);
    {
        setSpouse0(other);
    }
    
    protected void clearSpouse()
        //@ requires Person_spouse(this, _);
        //@ ensures Person_spouse(this, null);
    {
        clearSpouse0();
    }
    
    protected void ticketLemma()
        //@ requires Person_spouse(this, ?s) &*& s != null &*& Person_spouse(s, this);
        //@ ensures Person_spouse(this, s) &*& Person_spouse(s, this);
    {
    }
    
    public void symmetryLemma()
        //@ requires Person_spouse(this, ?s) &*& s != null &*& Person_spouse(s, this);
        //@ ensures Person_spouse(this, s) &*& Person_spouse(s, this);
    {
        Person spouse = getSpouse0();
        spouse.ticketLemma();
    }

    protected Person()
        //@ requires true;
        //@ ensures Person_spouse(this, null);
    {
        //@ close Person_spouse(this, null);
    }
    
    public static Person create()
        //@ requires true;
        //@ ensures Person_spouse(result, null) &*& result != null;
    {
        Person p = new Person();
        return p;
    }
    
    public Person getSpouse()
        //@ requires Person_spouse(this, ?s);
        //@ ensures Person_spouse(this, s) &*& result == s;
    {
        return getSpouse0();
    }
    
    void marry(Person other)
        //@ requires Person_spouse(this, _) &*& Person_spouse(other, _) &*& this != other;
        //@ ensures Person_spouse(this, other) &*& Person_spouse(other, this);
    {
        setSpouse0(other);
        other.setSpouse(this);
    }
    
    void divorce()
        //@ requires Person_spouse(this, ?s) &*& s != null &*& Person_spouse(s, _);
        //@ ensures Person_spouse(this, null) &*& Person_spouse(s, null);
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