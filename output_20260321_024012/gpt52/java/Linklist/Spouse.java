class Person {

    protected Person spouse;

    /*@
    predicate PersonInv() = this.spouse |-> ?s;
    @*/

    
    public  void spouse_symm()
        
        
    //@ requires PersonInv();
    //@ ensures PersonInv();
    {
        //@ open PersonInv();
        //@ close PersonInv();
        
        
    }

    public Person()
        
        
    //@ requires true;
    //@ ensures PersonInv();
    {
        //@ close PersonInv();
        
    }
    
    public Person getSpouse()
        
        
    //@ requires PersonInv();
    //@ ensures PersonInv() &*& result == spouse;
    {
        //@ open PersonInv();
        Person tmp = spouse;
        //@ close PersonInv();
        return tmp;
        
    }
    
    protected void setSpouse(Person other)
        
        
    //@ requires PersonInv() &*& other.PersonInv();
    //@ ensures PersonInv() &*& other.PersonInv();
    {
        //@ open PersonInv();
        //@ open other.PersonInv();
        spouse = other;
        other.spouse = this;
        //@ close other.PersonInv();
        //@ close PersonInv();
        
    }
    
    protected void clearSpouse()
        
        
    //@ requires PersonInv() &*& spouse != null &*& spouse.PersonInv();
    //@ ensures PersonInv();
    {
        //@ open PersonInv();
        Person s = spouse;
        //@ open s.PersonInv();
        spouse.spouse = null;
        //@ close s.PersonInv();
        spouse = null;
        //@ close PersonInv();
        
    }
    
    void marry(Person other)
        
        
    //@ requires PersonInv() &*& other.PersonInv();
    //@ ensures PersonInv() &*& other.PersonInv();
    {
        other.setSpouse(this);
        
    }
    
    void divorce()
        
        
    //@ requires PersonInv() &*& spouse != null &*& spouse.PersonInv();
    //@ ensures PersonInv() &*& spouse.PersonInv();
    {
        //@ open PersonInv();
        Person s = spouse;
        //@ close PersonInv();
        s.clearSpouse();
        
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