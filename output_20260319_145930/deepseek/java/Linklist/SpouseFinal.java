final class Person {

    private Person spouse;
    //@ predicate Person() = spouse |-> null;
    //@ predicate Married(Person o) = spouse |-> o &*& o.spouse |-> this;

    //@ requires true;
    //@ ensures Person();
    public Person()
    {
        //@ close Person();
    }
    
    //@ requires Person();
    //@ ensures Person() &*& result == spouse;
    public Person getSpouse()
    {
        //@ open Person();
        return spouse;
        //@ close Person();
    }
    
    //@ requires Person() &*& other != null &*& other.Person();
    //@ ensures Married(other) &*& other.Married(this);
    void marry(Person other)
    {
        //@ open Person();
        //@ open other.Person();
        spouse = other;
        other.spouse = this;
        //@ close Married(other);
        //@ close other.Married(this);
    }
    
    //@ requires Married(?other);
    //@ ensures Person() &*& other.Person();
    void divorce()
    {
        //@ open Married(?other);
        //@ open other.Married(this);
        spouse.spouse = null;
        spouse = null;
        //@ close Person();
        //@ close other.Person();
    }

}

class Program {

    //@ requires a != null &*& a.Person() &*& b != null &*& b.Person();
    //@ ensures a.Person() &*& b.Person();
    public static void foo(Person a, Person b)
    {
        //@ open a.Person();
        Person aSpouse = a.getSpouse();
        //@ close a.Person();
        //@ open b.Person();
        Person bSpouse = b.getSpouse();
        //@ close b.Person();
        if (aSpouse == b) {
            //@ assert bSpouse == a;
        }
    }

    //@ requires true;
    //@ ensures true;
    public static void main(String[] args)
    {
        Person a = new Person();
        Person b = new Person();
        a.marry(b);
        foo(a, b);
        b.divorce();
    }

}