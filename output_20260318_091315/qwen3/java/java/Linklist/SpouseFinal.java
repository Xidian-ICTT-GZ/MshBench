final class Person {

    private Person spouse;

    /*@ predicate spouse_of(Person p; Person s) =
        p.spouse |-> s;
    @*/

    public Person()
    //@ ensures spouse_of(this, null);
    {
    }
    
    public Person getSpouse()
    //@ requires spouse_of(this, ?s);
    //@ ensures spouse_of(this, s) &*& result == s;
    {
        return spouse;
    }
    
    void marry(Person other)
    //@ requires spouse_of(this, null) &*& spouse_of(other, null);
    //@ ensures spouse_of(this, other) &*& spouse_of(other, this);
    {
        spouse = other;
        other.spouse = this;
    }
    
    void divorce()
    //@ requires spouse_of(this, ?s) &*& spouse_of(s, this);
    //@ ensures spouse_of(this, null) &*& spouse_of(s, null);
    {
        spouse.spouse = null;
        spouse = null;
    }

}

class Program {

    public static void foo(Person a, Person b)
    //@ requires spouse_of(a, ?aSpouse) &*& spouse_of(b, ?bSpouse);
    //@ ensures spouse_of(a, aSpouse) &*& spouse_of(b, bSpouse);
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