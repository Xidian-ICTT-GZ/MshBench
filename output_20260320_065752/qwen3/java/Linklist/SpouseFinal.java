final class Person {

    private Person spouse;

    /*@
    predicate_family_instance person(Person p) = 
        p.spouse |-> ?s &*& 
        (s == null ? true : person(s));
    @*/

    public Person()
    //@ requires true;
    //@ ensures person(this);
    {
        //@ close person(this);
    }
    
    public Person getSpouse()
    //@ requires person(this);
    //@ ensures person(this) &*& result == this.spouse;
    {
        return spouse;
    }
    
    void marry(Person other)
    //@ requires person(this) &*& person(other) &*& this != other;
    //@ ensures person(this) &*& person(other);
    {
        //@ open person(this);
        //@ open person(other);
        spouse = other;
        other.spouse = this;
        //@ close person(other);
        //@ close person(this);
    }
    
    void divorce()
    //@ requires person(this) &*& this.spouse != null &*& person(this.spouse);
    //@ ensures person(this) &*& person(old_spouse);
    {
        Person old_spouse = spouse;
        //@ open person(this);
        //@ open person(old_spouse);
        spouse.spouse = null;
        spouse = null;
        //@ close person(old_spouse);
        //@ close person(this);
    }

}

class Program {

    public static void foo(Person a, Person b)
    //@ requires person(a) &*& person(b);
    //@ ensures person(a) &*& person(b);
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