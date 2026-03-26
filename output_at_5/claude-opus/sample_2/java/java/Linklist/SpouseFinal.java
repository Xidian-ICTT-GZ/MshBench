final class Person {

/*@
predicate person(Person this) = this.spouse |-> ?s &*& (s == null || person(s));
@*/

    private Person spouse;

    public Person()
    //@ requires true;
    //@ ensures person(this);
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
        //@ close person(this);
        //@ close person(other);
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
    //@ requires true;
    //@ ensures true;
    {
        Person aSpouse = a.getSpouse();
        Person bSpouse = b.getSpouse();
        if (aSpouse == b) {
            //@ assert bSpouse == a;
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