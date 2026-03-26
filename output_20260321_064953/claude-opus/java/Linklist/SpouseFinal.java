final class Person {

    private Person spouse;

    /*@
    predicate person(this) = this.spouse |-> ?s &*& (s == null || person(s));
    @*/

    //@ requires true;
    //@ ensures person(this);
    public Person()
    {
        //@ close person(this);
    }
    
    //@ requires person(this);
    //@ ensures person(this) &*& result == spouse;
    public Person getSpouse()
    {
        //@ open person(this);
        Person s = spouse;
        //@ close person(this);
        return s;
    }
    
    //@ requires person(this) &*& person(other);
    //@ ensures person(this) &*& person(other);
    void marry(Person other)
    {
        //@ open person(this);
        //@ open person(other);
        spouse = other;
        other.spouse = this;
        //@ close person(other);
        //@ close person(this);
    }
    
    //@ requires person(this);
    //@ ensures person(this);
    void divorce()
    {
        //@ open person(this);
        spouse.spouse = null;
        spouse = null;
        //@ close person(this);
    }

}

class Program {

    //@ requires person(a) &*& person(b);
    //@ ensures person(a) &*& person(b);
    public static void foo(Person a, Person b)
    {
        Person aSpouse = a.getSpouse();
        Person bSpouse = b.getSpouse();
        if (aSpouse == b) {
            assert bSpouse == a;
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