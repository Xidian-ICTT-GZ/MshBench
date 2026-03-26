class Person {

    protected Person spouse;

    













    
    public  void spouse_symm()
        
        
    {
        
        
        
    }

    public Person()
        
        
    {
        
    }
    
    public Person getSpouse()
        
        
    {
        
        return spouse;
        
    }
    
    protected void setSpouse(Person other)
        
        
    {
        
        spouse = other;
        other.spouse = this;
        
    }
    
    protected void clearSpouse()
        
        
    {
        
        spouse.spouse = null;
        spouse = null;
        
    }
    
    void marry(Person other)
        
        
    {
        
        other.setSpouse(this);
        
    }
    
    void divorce()
        
        
    {
        
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