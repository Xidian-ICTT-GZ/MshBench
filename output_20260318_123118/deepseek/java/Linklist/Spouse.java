class Person {

    protected Person spouse;

    //@ predicate valid() = this.spouse |-> ?sp &*& (sp == null ? emp : sp.spouse |-> this);
    //@ predicate married() = this.spouse |-> ?sp &*& sp != null &*& sp.spouse |-> this;
    //@ predicate single() = this.spouse |-> null;

    public  void spouse_symm()
        //@ requires valid();
        //@ ensures valid();
    {
        //@ open valid();
        //@ close valid();
    }

    public Person()
        //@ requires true;
        //@ ensures single();
    {
        spouse = null;
        //@ close single();
    }
    
    public Person getSpouse()
        //@ requires valid();
        //@ ensures valid() &*& result == spouse;
    {
        //@ open valid();
        Person result = spouse;
        //@ close valid();
        return result;
    }
    
    protected void setSpouse(Person other)
        //@ requires this.single() &*& other != null &*& other.single();
        //@ ensures this.married() &*& other.married();
    {
        //@ open single();
        //@ open other.single();
        spouse = other;
        other.spouse = this;
        //@ close married();
        //@ close other.married();
    }
    
    protected void clearSpouse()
        //@ requires married();
        //@ ensures single();
    {
        //@ open married();
        spouse.spouse = null;
        spouse = null;
        //@ close single();
    }
    
    void marry(Person other)
        //@ requires this.single() &*& other != null &*& other.single();
        //@ ensures this.married() &*& other.married();
    {
        other.setSpouse(this);
    }
    
    void divorce()
        //@ requires married();
        //@ ensures single();
    {
        //@ open married();
        spouse.clearSpouse();
        //@ close single();
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