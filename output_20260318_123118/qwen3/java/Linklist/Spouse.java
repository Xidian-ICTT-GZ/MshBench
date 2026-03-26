/*@ predicate spouse_of(Person p, Person s) = p.spouse |-> s; @*/

class Person {

    protected Person spouse;

    //@ requires true;
    //@ ensures true;
    public void spouse_symm()
    {
    }

    //@ requires true;
    //@ ensures spouse_of(this, null);
    public Person()
    {
    }
    
    //@ requires spouse_of(this, ?s);
    //@ ensures result == s &*& spouse_of(this, s);
    public Person getSpouse()
    {
        return spouse;
    }
    
    //@ requires spouse_of(this, null) &*& spouse_of(other, null);
    //@ ensures spouse_of(this, other) &*& spouse_of(other, this);
    protected void setSpouse(Person other)
    {
        spouse = other;
        other.spouse = this;
    }
    
    //@ requires spouse_of(this, ?s) &*& s != null &*& spouse_of(s, this);
    //@ ensures spouse_of(this, null) &*& spouse_of(s, null);
    protected void clearSpouse()
    {
        spouse.spouse = null;
        spouse = null;
    }
    
    //@ requires spouse_of(this, null) &*& spouse_of(other, null);
    //@ ensures spouse_of(this, other) &*& spouse_of(other, this);
    void marry(Person other)
    {
        other.setSpouse(this);
    }
    
    //@ requires spouse_of(this, ?s) &*& s != null &*& spouse_of(s, this);
    //@ ensures spouse_of(this, null) &*& spouse_of(s, null);
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