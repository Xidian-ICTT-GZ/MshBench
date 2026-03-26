final class Person {

    private Person spouse;

    /*@
    predicate person(Person p; Person s) =
        p.spouse |-> s;
    @*/

    public Person()
    //@ requires true;
    //@ ensures person(this, null);
    {
        //@ close person(this, null);
    }
    
    public Person getSpouse()
    //@ requires person(this, ?s);
    //@ ensures person(this, s) &*& result == s;
    {
        //@ open person(this, s);
        Person result = spouse;
        //@ close person(this, s);
        return result;
        
    }
    
    void marry(Person other)
    //@ requires person(this, null) &*& person(other, null) &*& this != other;
    //@ ensures person(this, other) &*& person(other, this);
    {
        //@ open person(this, null);
        //@ open person(other, null);
        
        spouse = other;
        other.spouse = this;
        
        //@ close person(this, other);
        //@ close person(other, this);
        
    }
    
    void divorce()
    //@ requires person(this, ?s) &*& s != null &*& person(s, this);
    //@ ensures person(this, null) &*& person(s, null);
    {
        //@ open person(this, s);
        //@ open person(s, this);
        
        spouse.spouse = null;
        spouse = null;
        
        //@ close person(s, null);
        //@ close person(this, null);
        
    }

}

class Program {

    public static void foo(Person a, Person b)
    //@ requires Person.person(a, ?as) &*& Person.person(b, ?bs);
    //@ ensures Person.person(a, as) &*& Person.person(b, bs);
    {
        Person aSpouse = a.getSpouse();
        Person bSpouse = b.getSpouse();
        if (aSpouse == b) {
            
            assert bSpouse == a;
        }
    }

    public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    {
        Person a = new Person();
        Person b = new Person();
        a.marry(b);
        foo(a, b);
        b.divorce();
    }

}