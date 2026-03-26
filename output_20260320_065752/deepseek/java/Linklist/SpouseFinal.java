final class Person {

    private Person spouse;
    //@ predicate Person() = spouse |-> null;
    //@ predicate married(Person o) = spouse |-> o &*& o != null &*& o.spouse |-> this;

    public Person()
        //@ requires true;
        //@ ensures Person();
    {
        //@ close Person();
    }
    
    public Person getSpouse()
        //@ requires Person();
        //@ ensures Person() &*& result == null ? true : married(result);
    {
        //@ open Person();
        return spouse;
        //@ close Person();
    }
    
    void marry(Person other)
        //@ requires Person() &*& other.Person();
        //@ ensures married(other) &*& other.married(this);
    {
        //@ open Person();
        //@ open other.Person();
        spouse = other;
        other.spouse = this;
        //@ close married(other);
        //@ close other.married(this);
    }
    
    void divorce()
        //@ requires married(?o);
        //@ ensures Person() &*& o.Person();
    {
        //@ open married(?o);
        spouse.spouse = null;
        spouse = null;
        //@ close Person();
        //@ close o.Person();
    }

}

class Program {

    public static void foo(Person a, Person b)
        //@ requires a.Person() &*& b.Person();
        //@ ensures a.Person() &*& b.Person();
    {
        Person aSpouse = a.getSpouse();
        Person bSpouse = b.getSpouse();
        if (aSpouse == b) {
            //@ open a.married(b);
            //@ assert bSpouse == a;
            //@ close a.married(b);
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