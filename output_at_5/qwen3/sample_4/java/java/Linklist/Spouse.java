class Person {

    protected Person spouse;
    
    /*@
    predicate person(Person p) = true;
    @*/

    public  void spouse_symm()
        
        
    {
        //@ requires true;
        //@ ensures true;
        
    }

    public Person()
        
        
    {
        //@ requires true;
        //@ ensures this.spouse == null;
        
    }
    
    public Person getSpouse()
        
        
    {
        //@ requires true;
        //@ ensures result == this.spouse;
        
        return spouse;
        
    }
    
    protected void setSpouse(Person other)
        
        
    {
        //@ requires true &*& other != null;
        //@ ensures this.spouse == other &*& other.spouse == this;
        
        spouse = other;
        other.spouse = this;
        
    }
    
    protected void clearSpouse()
        
        
    {
        //@ requires true &*& spouse != null;
        //@ ensures this.spouse == null &*& spouse.spouse == null;
        
        spouse.spouse = null;
        spouse = null;
        
    }
    
    void marry(Person other)
        
        
    {
        //@ requires true &*& other != null;
        //@ ensures true;
        
        other.setSpouse(this);
        
    }
    
    void divorce()
        
        
    {
        //@ requires true &*& spouse != null;
        //@ ensures this.spouse == null;
        
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