class Person {

    protected Person spouse;
    
    /*@
    predicate person(Person p) = true;
    @*/

    public  void spouse_symm()
        
        
    {
        //@ requires person(this);
        //@ ensures person(this);
        
    }

    public Person()
        
        
    {
        //@ requires true;
        //@ ensures person(this) &*& this.spouse == null;
        
    }
    
    public Person getSpouse()
        
        
    {
        //@ requires person(this);
        //@ ensures person(this) &*& result == this.spouse;
        
        return spouse;
        
    }
    
    protected void setSpouse(Person other)
        
        
    {
        //@ requires person(this) &*& person(other);
        //@ open person(this);
        //@ open person(other);
        //@ ensures person(this) &*& person(other);
        //@ close person(this);
        //@ close person(other);
        
        spouse = other;
        other.spouse = this;
        
    }
    
    protected void clearSpouse()
        
        
    {
        //@ requires person(this) &*& spouse != null;
        //@ open person(this);
        //@ open person(spouse);
        //@ ensures person(this) &*& person(spouse) &*& this.spouse == null;
        //@ close person(this);
        //@ close person(spouse);
        
        spouse.spouse = null;
        spouse = null;
        
    }
    
    void marry(Person other)
        
        
    {
        //@ requires person(this) &*& person(other);
        //@ open person(this);
        //@ open person(other);
        //@ ensures person(this) &*& person(other);
        //@ close person(this);
        //@ close person(other);
        
        other.setSpouse(this);
        
    }
    
    void divorce()
        
        
    {
        //@ requires person(this) &*& spouse != null;
        //@ open person(this);
        //@ open person(spouse);
        //@ ensures person(this) &*& person(spouse) &*& this.spouse == null;
        //@ close person(this);
        //@ close person(spouse);
        
        spouse.clearSpouse();
        
    }

}

class Program {

    public static void main(String[] args)
        
        
    {
        Person a = new Person();
        Person b = new Person();
        a.marry(b);
        b.divorce();
    }

}