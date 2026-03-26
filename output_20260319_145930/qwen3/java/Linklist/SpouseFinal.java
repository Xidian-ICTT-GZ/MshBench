final class Person {

    private Person spouse;

    /*@
    predicate_family_instance object_invariant(Person p) =
        true;
    @*/

    public Person()
    //@ requires true;
    //@ ensures object_invariant(this);
    {
        //@ close object_invariant(this);
    }
    
    public Person getSpouse()
    //@ requires object_invariant(this);
    //@ ensures object_invariant(this) &*& result == this.spouse;
    {
        return spouse;
    }
    
    void marry(Person other)
    //@ requires object_invariant(this) &*& object_invariant(other) &*& this != other;
    //@ ensures object_invariant(this) &*& object_invariant(other) &*& this.spouse == other &*& other.spouse == this;
    {
        //@ open object_invariant(this);
        //@ open object_invariant(other);
        spouse = other;
        other.spouse = this;
        //@ close object_invariant(this);
        //@ close object_invariant(other);
    }
    
    void divorce()
    //@ requires object_invariant(this) &*& this.spouse != null &*& object_invariant(this.spouse);
    //@ ensures object_invariant(this) &*& object_invariant(old_spouse) &*& this.spouse == null;
    {
        //@ open object_invariant(this);
        Person old_spouse = spouse;
        //@ open object_invariant(old_spouse);
        spouse.spouse = null;
        spouse = null;
        //@ close object_invariant(this);
        //@ close object_invariant(old_spouse);
    }

}

class Program {

    public static void foo(Person a, Person b)
    //@ requires object_invariant(a) &*& object_invariant(b);
    //@ ensures object_invariant(a) &*& object_invariant(b);
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