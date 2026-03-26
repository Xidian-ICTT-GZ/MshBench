class Person {

    protected Person spouse;

    /*@
    predicate PersonInv(Person p; Person s) =
        p.spouse |-> s;
    @*/

    
    public  void spouse_symm()
        
        
    //@ requires PersonInv(this, ?s) &*& s != null &*& PersonInv(s, this);
    //@ ensures PersonInv(this, s) &*& PersonInv(s, this);
    {
        //@ open PersonInv(this, s);
        //@ open PersonInv(s, this);
        //@ close PersonInv(s, this);
        //@ close PersonInv(this, s);
    }

    public Person()
        
        
    //@ requires true;
    //@ ensures PersonInv(this, null);
    {
        //@ close PersonInv(this, null);
    }
    
    public Person getSpouse()
        
        
    //@ requires PersonInv(this, ?s);
    //@ ensures PersonInv(this, s) &*& result == s;
    {
        //@ open PersonInv(this, s);
        Person result = spouse;
        //@ close PersonInv(this, s);
        return result;
        
    }
    
    protected void setSpouse(Person other)
        
        
    //@ requires PersonInv(this, ?s0) &*& PersonInv(other, ?s1);
    //@ ensures PersonInv(this, other) &*& PersonInv(other, this);
    {
        //@ open PersonInv(this, s0);
        //@ open PersonInv(other, s1);
        spouse = other;
        other.spouse = this;
        //@ close PersonInv(other, this);
        //@ close PersonInv(this, other);
        
    }
    
    protected void clearSpouse()
        
        
    //@ requires PersonInv(this, ?s) &*& s != null &*& PersonInv(s, this);
    //@ ensures PersonInv(this, null) &*& PersonInv(s, null);
    {
        //@ open PersonInv(this, s);
        //@ open PersonInv(s, this);
        spouse.spouse = null;
        spouse = null;
        //@ close PersonInv(s, null);
        //@ close PersonInv(this, null);
        
    }
    
    void marry(Person other)
        
        
    //@ requires PersonInv(this, ?s0) &*& PersonInv(other, ?s1);
    //@ ensures PersonInv(this, other) &*& PersonInv(other, this);
    {
        other.setSpouse(this);
        
    }
    
    void divorce()
        
        
    //@ requires PersonInv(this, ?s) &*& s != null &*& PersonInv(s, this);
    //@ ensures PersonInv(this, null) &*& PersonInv(s, null);
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
        //@ open Person.PersonInv(a, null);
        //@ open Person.PersonInv(b, null);
        a.marry(b);
        //@ open Person.PersonInv(a, b);
        //@ open Person.PersonInv(b, a);
        b.divorce();
        //@ close Person.PersonInv(a, null);
        //@ close Person.PersonInv(b, null);
    }

}