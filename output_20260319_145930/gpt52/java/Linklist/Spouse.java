/*@

predicate person(Person p; Person s) =
    p.spouse |-> s;

@*/

class Person {

    protected Person spouse;

    public void spouse_symm()
    //@ requires true;
    //@ ensures true;
    {
    }

    public Person()
    //@ requires true;
    //@ ensures person(this, null);
    {
        //@ close person(this, null);
    }

    public Person getSpouse()
    //@ requires person(this, ?s);
    //@ ensures person(this, s) &*& result == s;
    {
        //@ open person(this, ?s0);
        Person res = spouse;
        //@ close person(this, s0);
        return res;
    }

    protected void setSpouse(Person other)
    //@ requires person(this, null) &*& person(other, null);
    //@ ensures person(this, other) &*& person(other, this);
    {
        //@ open person(this, _);
        //@ open person(other, _);
        spouse = other;
        other.spouse = this;
        //@ close person(this, other);
        //@ close person(other, this);
    }

    protected void clearSpouse()
    //@ requires person(this, ?s) &*& s != null &*& person(s, this);
    //@ ensures person(this, null) &*& person(s, null);
    {
        //@ open person(this, ?s0);
        //@ open person(s0, _);
        spouse.spouse = null;
        spouse = null;
        //@ close person(s0, null);
        //@ close person(this, null);
    }

    void marry(Person other)
    //@ requires person(this, null) &*& person(other, null);
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
        //@ assert person(a, null);
        Person b = new Person();
        //@ assert person(b, null);
        a.marry(b);
        //@ assert person(a, b) &*& person(b, a);
        b.divorce();
        //@ assert person(a, null) &*& person(b, null);
        //@ open person(a, _);
        //@ open person(b, _);
    }

}