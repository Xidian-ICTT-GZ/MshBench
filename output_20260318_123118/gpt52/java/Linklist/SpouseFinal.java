final class Person {

    private Person spouse;

    /*@ predicate person(Person p; Person s) =
            p != null
        &*& p.spouse |-> s;
    @*/

    public Person()
    //@ requires true;
    //@ ensures person(this, null);
    {
    }

    public Person getSpouse()
    //@ requires person(this, ?s);
    //@ ensures person(this, s) &*& result == s;
    {
        return spouse;
    }

    void marry(Person other)
    //@ requires person(this, null) &*& person(other, null) &*& this != other;
    //@ ensures person(this, other) &*& person(other, this);
    {
        spouse = other;
        other.spouse = this;
    }

    void divorce()
    //@ requires person(this, ?s) &*& s != null &*& person(s, this);
    //@ ensures person(this, null) &*& person(s, null);
    {
        spouse.spouse = null;
        spouse = null;
    }

}

class Program {

    public static void foo(Person a, Person b)
    //@ requires Person.person(a, b) &*& Person.person(b, a);
    //@ ensures Person.person(a, b) &*& Person.person(b, a);
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