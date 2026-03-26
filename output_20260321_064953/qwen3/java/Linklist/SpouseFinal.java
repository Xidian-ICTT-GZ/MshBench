final class Person {

    private Person spouse;

    /*@
    predicate_family_instance person(Person p) = 
        p.spouse |-> ?s &*& 
        (s == null ? true : person(s));
    @*/

    public Person()
        
        
    {
        
        //@ close person(this);
    }
    
    public Person getSpouse()
        
        
    {
        
        //@ open person(this);
        //@ close person(this);
        return spouse;
        
    }
    
    void marry(Person other)
        
        
    {
        
        
        //@ open person(this);
        //@ open person(other);
        spouse = other;
        other.spouse = this;
        //@ close person(other);
        //@ close person(this);
        
        
    }
    
    void divorce()
        
        
    {
        
        
        //@ open person(this);
        if (spouse != null) {
            //@ open person(spouse);
            spouse.spouse = null;
            //@ close person(spouse);
        }
        spouse = null;
        //@ close person(this);
        
        
    }

}

class Program {

    public static void foo(Person a, Person b)
        
        
    {
        //@ open person(a);
        //@ open person(b);
        Person aSpouse = a.getSpouse();
        Person bSpouse = b.getSpouse();
        if (aSpouse == b) {
            
            assert bSpouse == a;
        }
        //@ close person(b);
        //@ close person(a);
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