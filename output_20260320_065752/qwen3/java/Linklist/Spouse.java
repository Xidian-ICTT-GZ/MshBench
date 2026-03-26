/*@ predicate person(Person p; Person spouse) = p.spouse |-> spouse; @*/

class Person {

    protected Person spouse;

    
    //@ requires person(this, _) &*& person(other, _);
    //@ ensures person(this, other) &*& person(other, this);
    public  void spouse_symm()
    {
        //@ open person(this, _);
        //@ open person(other, _);
        spouse = other;
        other.spouse = this;
        //@ close person(this, other);
        //@ close person(other, this);
    }

    //@ ensures person(this, null);
    public Person()
    {
        //@ close person(this, null);
    }
    
    //@ requires person(this, ?s);
    //@ ensures person(this, s) &*& result == s;
    public Person getSpouse()
    {
        //@ open person(this, _);
        //@ close person(this, spouse);
        return spouse;
    }
    
    //@ requires person(this, _) &*& person(other, _);
    //@ ensures person(this, other) &*& person(other, this);
    protected void setSpouse(Person other)
    {
        //@ open person(this, _);
        //@ open person(other, _);
        spouse = other;
        other.spouse = this;
        //@ close person(this, other);
        //@ close person(other, this);
    }
    
    //@ requires person(this, ?s) &*& s != null &*& person(s, this);
    //@ ensures person(this, null) &*& person(s, null);
    protected void clearSpouse()
    {
        //@ open person(this, ?s);
        //@ open person(s, this);
        spouse.spouse = null;
        spouse = null;
        //@ close person(this, null);
        //@ close person(s, null);
    }
    
    //@ requires person(this, _) &*& person(other, _);
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