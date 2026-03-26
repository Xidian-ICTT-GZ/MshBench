



class Person {

    private Person spouse;

    







    
    protected Person getSpouse0()
        
        
    {
        
        Person result = spouse;
        
        return result;
    }
    
    protected void setSpouse0(Person other)
        
        
    {
        
        spouse = other;
        
        
    }
    
    protected void clearSpouse0()
        
        
    {
        
        
        spouse = null;
        
    }
    
    protected void setSpouse(Person other)
        
        
    {
        
        setSpouse0(other);
        
    }
    
    protected void clearSpouse()
        
        
    {
        
        clearSpouse0();
        
    }
    
    












    
    protected  void ticketLemma()
        
        
    {
        
        
        
    }
    
    public  void symmetryLemma()
        
        
    {
        
        Person spouse = getSpouse0();
        spouse.ticketLemma();
        
    }

    protected Person()
        
        
    {
        
    }
    
    









    
    public static Person create()
        
        
    {
        Person p = new Person();
        
        return p;
    }
    
    public Person getSpouse()
        
        
    {
        
        return getSpouse0();
        
    }
    
    void marry(Person other)
        
        
    {
        
        setSpouse0(other);
        other.setSpouse(this);
        
    }
    
    void divorce()
        
        
    {
        
        Person spouse = getSpouse0();
        spouse.clearSpouse();
        clearSpouse0();
        
    }

}

class Program {

    public static void main(String[] args)
        
        
    {
        Person a = Person.create();
        Person b = Person.create();
        a.marry(b);
        b.divorce();
    }

}