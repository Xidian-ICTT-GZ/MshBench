class Person {

    protected Person spouse;

    /*@ 
    predicate person(this, spouse_) = 
        this.spouse |-> spouse_ &*&
        (spouse_ == null || spouse_.spouse == this);
    @*/

    //@ requires person(this, ?s);
    //@ ensures person(this, s);
    public void spouse_symm()
    {
    }

    //@ requires true;
    //@ ensures person(this, null);
    public Person()
    {
    }

    //@ requires person(this, ?s);
    //@ ensures person(this, s) &*& result == s;
    public Person getSpouse()
    {
        return spouse;
    }

    //@ requires person(this, ?s) &*& person(other, ?o) &*& s == null &*& o == null;
    //@ ensures person(this, other) &*& person(other, this);
    protected void setSpouse(Person other)
    {
        spouse = other;
        other.spouse = this;
    }

    //@ requires person(this, ?s) &*& s != null &*& person(s, this);
    //@ ensures person(this, null) &*& person(s, null);
    protected void clearSpouse()
    {
        spouse.spouse = null;
        spouse = null;
    }

    //@ requires person(this, null) &*& person(other, null);
    //@ ensures person(this, other) &*& person(other, this);
    void marry(Person other)
    {
        other.setSpouse(this);
    }

    //@ requires person(this, ?s) &*& s != null &*& person(s, this);
    //@ ensures person(this, null) &*& person(s, null);
    void divorce()
    {
        spouse.clearSpouse();
    }

}

class Program {

    //@ requires true;
    //@ ensures true;
    public static void main(String[] args)
    {
        Person a = new Person();
        Person b = new Person();
        a.marry(b);
        b.divorce();
    }

}