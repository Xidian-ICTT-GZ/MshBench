final class Person {

    private Person spouse;
    //@ predicate Person() = spouse == null;
    //@ predicate married(Person o) = spouse == o &*& o != null &*& o.spouse == this;

    public Person()
        //@ requires true;
        //@ ensures Person();
    {
        //@ close Person();
    }
    
    public Person getSpouse()
        //@ requires Person();
        //@ ensures Person() &*& result == spouse;
    {
        //@ open Person();
        return spouse;
        //@ close Person();
    }
    
    void marry(Person other)
        //@ requires Person() &*& other != null &*& other.Person();
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
        //@ requires married(?other);
        //@ ensures Person() &*& other.Person();
    {
        //@ open married(other);
        //@ open other.married(this);
        spouse.spouse = null;
        spouse = null;
        //@ close Person();
        //@ close other.Person();
    }

}

class Program {

    public static void foo(Person a, Person b)
        //@ requires a.married(?b0) &*& b0 == b &*& b.married(?a0) &*& a0 == a;
        //@ ensures a.married(b) &*& b.married(a);
    {
        //@ open a.married(b);
        Person aSpouse = a.getSpouse();
        //@ open b.married(a);
        Person bSpouse = b.getSpouse();
        if (aSpouse == b) {
            //@ assert bSpouse == a;
        }
        //@ close a.married(b);
        //@ close b.married(a);
    }

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        Person a = new Person();
        Person b = new Person();
        a.marry(b);
        //@ assert a.married(b);
        //@ assert b.married(a);
        foo(a, b);
        b.divorce();
    }

}