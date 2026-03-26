final class Person {

    /*@
    predicate person(this) = this.spouse |-> ?s &*& (s == null || person(s));
    @*/

    private Person spouse;

    //@ invariant person(this);

    public Person()
        //@ requires true;
        //@ ensures person(result);
    {
        spouse = null;
    }
    
    public Person getSpouse()
        //@ requires person(this);
        //@ ensures person(this) &*& result == spouse;
    {
        return spouse;
    }
    
    void marry(Person other)
        //@ requires person(this) &*& person(other);
        //@ ensures person(this) &*& person(other) &*& spouse == other &*& other.spouse == this;
    {
        //@ open person(this);
        //@ open person(other);
        spouse = other;
        other.spouse = this;
        //@ close person(other);
        //@ close person(this);
    }
    
    void divorce()
        //@ requires person(this) &*& spouse != null &*& person(spouse);
        //@ ensures person(this) &*& spouse == null;
    {
        //@ open person(this);
        //@ open person(spouse);
        spouse.spouse = null;
        spouse = null;
        //@ close person(this);
    }

}

class Program {

    public static void foo(Person a, Person b)
        //@ requires a.person() &*& b.person();
        //@ ensures a.person() &*& b.person();
    {
        Person aSpouse = a.getSpouse();
        Person bSpouse = b.getSpouse();
        if (aSpouse == b) {
            //@ open a.person();
            //@ open b.person();
            assert bSpouse == a;
            //@ close a.person();
            //@ close b.person();
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