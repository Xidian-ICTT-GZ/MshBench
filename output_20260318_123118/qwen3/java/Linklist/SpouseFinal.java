final class Person {

    private Person spouse;

    /*@ predicate valid() = 
        (spouse == null &*& true) || 
        (spouse != null &*& spouse.spouse == this &*& spouse.valid());
    @*/

    public Person()
    //@ ensures valid();
    {
    }
    
    public Person getSpouse()
    //@ requires valid();
    //@ ensures valid() &*& result == spouse;
    {
        return spouse;
    }
    
    void marry(Person other)
    //@ requires valid() &*& other.valid() &*& spouse == null &*& other.spouse == null;
    //@ ensures valid() &*& other.valid() &*& spouse == other &*& other.spouse == this;
    {
        spouse = other;
        other.spouse = this;
    }
    
    void divorce()
    //@ requires valid() &*& spouse != null;
    //@ ensures valid() &*& spouse == null &*& old(spouse).valid() &*& old(spouse).spouse == null;
    {
        spouse.spouse = null;
        spouse = null;
    }

}

class Program {

    public static void foo(Person a, Person b)
    //@ requires a.valid() &*& b.valid();
    //@ ensures a.valid() &*& b.valid();
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