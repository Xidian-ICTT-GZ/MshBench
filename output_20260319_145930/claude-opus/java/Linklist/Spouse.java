class Person {

    protected Person spouse;

    /*@
    predicate person(Person s;) = this.spouse |-> s;
    @*/

    /*@
    predicate married(Person s;) = this.spouse |-> s &*& s != null &*& s.spouse |-> this;
    @*/

    public void spouse_symm()
        //@ requires true;
        //@ ensures true;
    {
    }

    public Person()
        //@ requires true;
        //@ ensures this.person(null);
    {
        //@ close this.person(null);
    }
    
    public Person getSpouse()
        //@ requires this.person(?s);
        //@ ensures this.person(s) &*& result == s;
    {
        //@ open this.person(s);
        Person result = spouse;
        //@ close this.person(s);
        return result;
    }
    
    protected void setSpouse(Person other)
        //@ requires this.person(null) &*& other.person(null) &*& other != this;
        //@ ensures this.married(other);
    {
        //@ open this.person(null);
        //@ open other.person(null);
        spouse = other;
        other.spouse = this;
        //@ close this.married(other);
    }
    
    protected void clearSpouse()
        //@ requires this.married(?s);
        //@ ensures this.person(null) &*& s.person(null);
    {
        //@ open this.married(s);
        spouse.spouse = null;
        //@ close s.person(null);
        spouse = null;
        //@ close this.person(null);
    }
    
    void marry(Person other)
        //@ requires this.person(null) &*& other.person(null) &*& other != this;
        //@ ensures other.married(this);
    {
        other.setSpouse(this);
    }
    
    void divorce()
        //@ requires this.married(?s);
        //@ ensures this.person(null) &*& s.person(null);
    {
        //@ open this.married(s);
        //@ close spouse.married(this);
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
        a.marry(b);
        //@ assert b.married(a);
        //@ open b.married(a);
        //@ close a.married(b);
        b.divorce();
    }

}