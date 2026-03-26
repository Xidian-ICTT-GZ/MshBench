class Person {

    protected Person spouse;

    /*@
    predicate person(Person p; Person s) = p.spouse |-> s;
    @*/

    
    public  void spouse_symm()
        
        
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
        //@ open person(this, s);
        Person result_ = spouse;
        //@ close person(this, s);
        return result_;
        
    }
    
    protected void setSpouse(Person other)
        
        
    //@ requires person(this, _) &*& person(other, _);
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
        //@ open person(this, s);
        //@ open person(s, this);
        spouse.spouse = null;
        spouse = null;
        //@ close person(s, null);
        //@ close person(this, null);
        
    }
    
    void marry(Person other)
        
        
    //@ requires person(this, _) &*& person(other, _);
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
        //@ open person(b, a);
        b.divorce();
        //@ open person(b, null);
        //@ open person(a, null);
    }

}