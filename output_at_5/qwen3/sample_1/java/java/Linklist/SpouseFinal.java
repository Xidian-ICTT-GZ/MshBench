final class Person {

    private Person spouse;

    /*@
    predicate married(Person a, Person b) =
        a.spouse == b && b.spouse == a;
    @*/

    public Person()
        
        
    {
        
    }
    
    public Person getSpouse()
        
        
    {
        
        return spouse;
        
    }
    
    void marry(Person other)
        
        
    {
        //@ requires true;
        //@ ensures true;
        //@ open Person(spouse);
        if (spouse != null) {
            //@ close Person(spouse);
            //@ open Person(other.spouse);
            other.spouse = this;
            //@ close Person(other.spouse);
        }
        spouse = other;
        //@ close Person(spouse);
    }
    
    void divorce()
        
        
    {
        //@ requires spouse != null;
        //@ ensures true;
        //@ open Person(spouse);
        spouse.spouse = null;
        spouse = null;
        //@ close Person(spouse);
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