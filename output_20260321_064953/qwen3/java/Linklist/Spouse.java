class Person {

    protected Person spouse;

    /*@
    predicate_family_instance spouse_inv(Person p; Person s) =
        p.spouse |-> s;
    @*/

    //@ requires [?f]spouse_inv(this, ?s);
    //@ ensures [f]spouse_inv(this, s);
    public  void spouse_symm()
    {
    }

    //@ ensures spouse_inv(this, null);
    public Person()
    {
        //@ close spouse_inv(this, null);
    }
    
    //@ requires [?f]spouse_inv(this, ?s);
    //@ ensures [f]spouse_inv(this, s) &*& result == s;
    public Person getSpouse()
    {
        return spouse;
    }
    
    //@ requires spouse_inv(this, ?s1) &*& spouse_inv(other, ?s2);
    //@ ensures spouse_inv(this, other) &*& spouse_inv(other, this);
    protected void setSpouse(Person other)
    {
        //@ open spouse_inv(this, s1);
        //@ open spouse_inv(other, s2);
        spouse = other;
        other.spouse = this;
        //@ close spouse_inv(this, other);
        //@ close spouse_inv(other, this);
    }
    
    //@ requires spouse_inv(this, ?s) &*& s != null &*& spouse_inv(s, this);
    //@ ensures spouse_inv(this, null) &*& spouse_inv(s, null);
    protected void clearSpouse()
    {
        //@ open spouse_inv(this, s);
        //@ open spouse_inv(s, this);
        spouse.spouse = null;
        spouse = null;
        //@ close spouse_inv(this, null);
        //@ close spouse_inv(s, null);
    }
    
    //@ requires spouse_inv(this, null) &*& spouse_inv(other, null);
    //@ ensures spouse_inv(this, other) &*& spouse_inv(other, this);
    void marry(Person other)
    {
        other.setSpouse(this);
    }
    
    //@ requires spouse_inv(this, ?s) &*& s != null &*& spouse_inv(s, this);
    //@ ensures spouse_inv(this, null) &*& spouse_inv(s, null);
    void divorce()
    {
        spouse.clearSpouse();
    }

}

class Program {

    public static void main(String[] args)
    {
        //@ close Person.spouse_inv(a, null);
        Person a = new Person();
        //@ close Person.spouse_inv(b, null);
        Person b = new Person();
        a.marry(b);
        b.divorce();
    }

}