final class Person {

    private Person spouse;

    public Person()
        
        
    {
        
    }
    
    public Person getSpouse()
        
        
    {
        
        return spouse;
        
    }
    
    void marry(Person other)
        
        
    {
        
        
        spouse = other;
        if (other != null) {
            other.spouse = this;
        }
        
        
    }
    
    void divorce()
        
        
    {
        
        
        if (spouse != null) {
            spouse.spouse = null;
            spouse = null;
        }
        
        
    }

}

class Program {

    public static void foo(Person a, Person b)
        
        
    {
        Person aSpouse = a.getSpouse();
        Person bSpouse = b.getSpouse();
        if (aSpouse == b) {
            
            assert bSpouse == a;
        }
    }

    public static void main(String[] args)
        
        
    {
        Person a = new Person();
        Person b = new Person();
        a.marry(b);
        foo(a, b);
        b.divorce();
    }

}