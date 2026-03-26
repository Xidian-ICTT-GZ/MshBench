class Person {

    protected Person spouse;

    /*@
    predicate PersonObj(Person p; Person s) =
        p.spouse |-> s;
    @*/

    
    public  void spouse_symm()
        
        
    //@ requires PersonObj(this, ?s);
    //@ ensures PersonObj(this, s);
    {
        //@ open PersonObj(this, s);
        //@ close PersonObj(this, s);
        
        
    }

    public Person()
        
        
    //@ requires true;
    //@ ensures PersonObj(this, null);
    {
        //@ close PersonObj(this, null);
        
    }
    
    public Person getSpouse()
        
        
    //@ requires PersonObj(this, ?s);
    //@ ensures PersonObj(this, s) &*& result == s;
    {
        //@ open PersonObj(this, s);
        Person tmp = spouse;
        //@ close PersonObj(this, s);
        return tmp;
        
    }
    
    protected void setSpouse(Person other)
        
        
    //@ requires PersonObj(this, ?s0) &*& PersonObj(other, ?s1);
    //@ ensures PersonObj(this, other) &*& PersonObj(other, this);
    {
        //@ open PersonObj(this, s0);
        //@ open PersonObj(other, s1);
        spouse = other;
        other.spouse = this;
        //@ close PersonObj(other, this);
        //@ close PersonObj(this, other);
        
    }
    
    protected void clearSpouse()
        
        
    //@ requires PersonObj(this, ?s) &*& PersonObj(s, this);
    //@ ensures PersonObj(this, null) &*& PersonObj(s, null);
    {
        //@ open PersonObj(this, s);
        //@ open PersonObj(s, this);
        spouse.spouse = null;
        spouse = null;
        //@ close PersonObj(s, null);
        //@ close PersonObj(this, null);
        
    }
    
    void marry(Person other)
        
        
    //@ requires PersonObj(this, ?s0) &*& PersonObj(other, ?s1);
    //@ ensures PersonObj(this, other) &*& PersonObj(other, this);
    {
        
        other.setSpouse(this);
        
    }
    
    void divorce()
        
        
    //@ requires PersonObj(this, ?s) &*& PersonObj(s, this);
    //@ ensures PersonObj(this, null) &*& PersonObj(s, null);
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
        //@ open PersonObj(a, null);
        //@ open PersonObj(b, null);
        //@ close PersonObj(a, null);
        //@ close PersonObj(b, null);
        a.marry(b);
        //@ open PersonObj(a, b);
        //@ open PersonObj(b, a);
        //@ close PersonObj(a, b);
        //@ close PersonObj(b, a);
        b.divorce();
        //@ open PersonObj(b, null);
        //@ open PersonObj(a, null);
        //@ close PersonObj(b, null);
        //@ close PersonObj(a, null);
    }

}