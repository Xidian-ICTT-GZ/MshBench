final class Person {

    private Person spouse;

    /*@
    predicate Person(Person spouse;) =
        this.spouse |-> spouse;
    
    predicate married(Person spouse;) =
        this.spouse |-> spouse &*& spouse != null &*& spouse.spouse |-> this;
    @*/

    public Person()
        //@ requires true;
        //@ ensures Person(null);
    {
        //@ close Person(null);
    }
    
    public Person getSpouse()
        //@ requires Person(?s);
        //@ ensures Person(s) &*& result == s;
    {
        //@ open Person(s);
        Person result = spouse;
        //@ close Person(s);
        return result;
    }
    
    void marry(Person other)
        //@ requires Person(null) &*& other.Person(null) &*& other != this;
        //@ ensures married(other);
    {
        //@ open Person(null);
        //@ open other.Person(null);
        spouse = other;
        other.spouse = this;
        //@ close married(other);
    }
    
    void divorce()
        //@ requires married(?other);
        //@ ensures Person(null) &*& other.Person(null);
    {
        //@ open married(other);
        spouse.spouse = null;
        spouse = null;
        //@ close other.Person(null);
        //@ close Person(null);
    }

}

class Program {

    public static void foo(Person a, Person b)
        //@ requires a.married(b);
        //@ ensures a.married(b);
    {
        //@ open a.married(b);
        //@ close a.Person(b);
        Person aSpouse = a.getSpouse();
        //@ open a.Person(b);
        //@ close b.Person(a);
        Person bSpouse = b.getSpouse();
        //@ open b.Person(a);
        if (aSpouse == b) {
            assert bSpouse == a;
        }
        //@ close a.married(b);
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