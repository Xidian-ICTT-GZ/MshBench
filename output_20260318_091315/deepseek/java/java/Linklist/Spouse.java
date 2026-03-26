class Person {

    protected Person spouse;

    /*@
    predicate valid() =
        this.spouse |-> ?s &*&
        (s == null ? true : s.spouse |-> this);
    @*/

    /*@
    predicate married() =
        this.spouse |-> ?s &*& s != null &*& s.spouse |-> this;
    @*/

    /*@
    predicate single() =
        this.spouse |-> null;
    @*/

    //@ requires true;
    //@ ensures valid();
    public  void spouse_symm()
    //@ requires valid();
    //@ ensures valid();
    {
        
    }

    //@ requires true;
    //@ ensures single();
    public Person()
    {
        //@ close single();
    }
    
    //@ requires valid();
    //@ ensures valid() &*& result == spouse;
    public Person getSpouse()
    {
        //@ open valid();
        return spouse;
        //@ close valid();
    }
    
    //@ requires this.single() &*& other.single();
    //@ ensures this.married() &*& other.married();
    protected void setSpouse(Person other)
    {
        //@ open this.single();
        //@ open other.single();
        spouse = other;
        other.spouse = this;
        //@ close this.married();
        //@ close other.married();
    }
    
    //@ requires this.married();
    //@ ensures this.single() &*& other.single();
    protected void clearSpouse()
    {
        //@ open this.married();
        spouse.spouse = null;
        spouse = null;
        //@ close this.single();
        //@ close other.single();
    }
    
    //@ requires this.single() &*& other.single();
    //@ ensures this.married() &*& other.married();
    void marry(Person other)
    {
        other.setSpouse(this);
    }
    
    //@ requires this.married();
    //@ ensures this.single() &*& other.single();
    void divorce()
    {
        //@ open this.married();
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
        b.divorce();
    }

}