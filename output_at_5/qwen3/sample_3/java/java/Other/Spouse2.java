class Person {

    private Person spouse;
    
    /*@
    predicate person(Person p) = true;
    @*/
    
    protected Person getSpouse0()
        //@ requires true;
        //@ ensures result == null || person(result);
    {
        
        Person result = spouse;
        
        return result;
    }
    
    protected void setSpouse0(Person other)
        //@ requires other == null || person(other);
    {
        
        spouse = other;
        
        
    }
    
    protected void clearSpouse0()
        //@ requires true;
    {
        
        
        spouse = null;
        
    }
    
    protected void setSpouse(Person other)
        //@ requires other == null || person(other);
    {
        
        setSpouse0(other);
        
    }
    
    protected void clearSpouse()
        //@ requires true;
    {
        
        clearSpouse0();
        
    }
    
    

    
    protected  void ticketLemma()
        //@ requires true;
        //@ ensures true;
    {
        
        
        
    }
    
    public  void symmetryLemma()
        //@ requires true;
        //@ ensures true;
    {
        
        Person spouse = getSpouse0();
        if (spouse != null) {
            spouse.ticketLemma();
        }
        
    }

    protected Person()
        //@ ensures person(this);
    {
        
    }
    
    

    
    public static Person create()
        //@ ensures person(result);
    {
        Person p = new Person();
        
        return p;
    }
    
    public Person getSpouse()
        //@ requires true;
        //@ ensures result == null || person(result);
    {
        
        return getSpouse0();
        
    }
    
    void marry(Person other)
        //@ requires true;
        //@ ensures true;
    {
        
        setSpouse0(other);
        other.setSpouse(this);
        
    }
    
    void divorce()
        //@ requires true;
        //@ ensures true;
    {
        
        Person spouse = getSpouse0();
        if (spouse != null) {
            spouse.clearSpouse();
        }
        clearSpouse0();
        
    }

}

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        Person a = Person.create();
        Person b = Person.create();
        a.marry(b);
        b.divorce();
    }

}