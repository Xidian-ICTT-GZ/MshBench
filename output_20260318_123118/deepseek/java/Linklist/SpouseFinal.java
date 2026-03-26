final class Person {

    private Person spouse;

    /*@
    predicate valid() =
        this.spouse |-> ?s &*&
        (s == null ? true : s.spouse |-> this);
    @*/

    //@ requires true;
    //@ ensures valid();
    public Person()
    {
        //@ close valid();
    }
    
    //@ requires valid();
    //@ ensures valid() &*& result == spouse;
    public Person getSpouse()
    {
        //@ open valid();
        return spouse;
        //@ close valid();
    }
    
    //@ requires other != null &*& valid() &*& other.valid() &*& spouse == null &*& other.spouse == null;
    //@ ensures valid() &*& other.valid();
    void marry(Person other)
    {
        //@ open valid();
        //@ open other.valid();
        spouse = other;
        other.spouse = this;
        //@ close other.valid();
        //@ close valid();
    }
    
    //@ requires valid() &*& spouse != null;
    //@ ensures valid();
    void divorce()
    {
        //@ open valid();
        //@ open spouse.valid();
        spouse.spouse = null;
        spouse = null;
        //@ close spouse.valid();
        //@ close valid();
    }

}

class Program {

    //@ requires a != null &*& b != null &*& a.valid() &*& b.valid();
    //@ ensures a.valid() &*& b.valid();
    public static void foo(Person a, Person b)
    {
        //@ open a.valid();
        Person aSpouse = a.getSpouse();
        //@ close a.valid();
        //@ open b.valid();
        Person bSpouse = b.getSpouse();
        //@ close b.valid();
        if (aSpouse == b) {
            //@ open a.valid();
            //@ open b.valid();
            //@ assert bSpouse == a;
            //@ close b.valid();
            //@ close a.valid();
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