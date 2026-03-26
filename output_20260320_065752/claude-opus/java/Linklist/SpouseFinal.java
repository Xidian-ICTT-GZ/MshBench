final class Person {

    private Person spouse;
    
    /*@
    predicate inv(Person p) = true;
    @*/

    public Person()
        //@ requires true;
        //@ ensures inv(this);
    {
        
    }
    
    public Person getSpouse()
        //@ requires inv(this);
        //@ ensures inv(this) &*& result == spouse;
    {
        return spouse;
    }
    
    void marry(Person other)
        //@ requires inv(this) &*& inv(other);
        //@ ensures inv(this) &*& inv(other) &*& spouse == other &*& other.spouse == this;
    {
        spouse = other;
        other.spouse = this;
    }
    
    void divorce()
        //@ requires inv(this) &*& spouse != null &*& inv(spouse);
        //@ ensures inv(this) &*& (spouse == null);
    {
        spouse.spouse = null;
        spouse = null;
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