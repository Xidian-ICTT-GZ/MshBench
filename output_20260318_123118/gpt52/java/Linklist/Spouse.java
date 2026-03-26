class Person {

    protected Person spouse;

    /*@ predicate person(Person p; Person s) =
            p.spouse |-> s;
    @*/

    public void spouse_symm()
        //@ requires person(this, ?s);
        //@ ensures person(this, s);
    {
    }

    public Person()
        //@ requires true;
        //@ ensures person(this, null);
    {
    }
    
    public Person getSpouse()
        //@ requires person(this, ?s);
        //@ ensures person(this, s) &*& result == s;
    {
        return spouse;
    }
    
    protected void setSpouse(Person other)
        //@ requires person(this, ?s0) &*& person(other, ?s1);
        //@ ensures person(this, other) &*& person(other, this);
    {
        spouse = other;
        other.spouse = this;
    }
    
    protected void clearSpouse()
        //@ requires person(this, ?s) &*& s != null &*& person(s, this);
        //@ ensures person(this, null) &*& person(s, null);
    {
        spouse.spouse = null;
        spouse = null;
    }
    
    void marry(Person other)
        //@ requires person(this, ?s0) &*& person(other, ?s1);
        //@ ensures person(this, other) &*& person(other, this);
    {
        other.setSpouse(this);
    }
    
    void divorce()
        //@ requires person(this, ?s) &*& s != null &*& person(s, this);
        //@ ensures person(this, null) &*& person(s, null);
    {
        spouse.clearSpouse();
    }

}

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        Person a = new Person();
        Person b = new Person();
        //@ open person(a, null);
        //@ open person(b, null);
        a.marry(b);
        //@ open person(a, b);
        //@ open person(b, a);
        b.divorce();
        //@ open person(a, null);
        //@ open person(b, null);
    }

}