final class Person {

    private Person spouse;

    /*@
    predicate PersonInv(Person p; Person s) =
        p.spouse |-> s;
    @*/

    public Person()
    //@ requires true;
    //@ ensures PersonInv(this, null);
    {
        //@ close PersonInv(this, null);
    }
    
    public Person getSpouse()
    //@ requires PersonInv(this, ?s);
    //@ ensures PersonInv(this, s) &*& result == s;
    {
        //@ open PersonInv(this, ?s0);
        Person tmp = spouse;
        //@ close PersonInv(this, s0);
        return tmp;
        
    }
    
    void marry(Person other)
    //@ requires PersonInv(this, ?s1) &*& PersonInv(other, ?s2);
    //@ ensures PersonInv(this, other) &*& PersonInv(other, this);
    {
        
        
        //@ open PersonInv(this, ?s1_);
        //@ open PersonInv(other, ?s2_);
        spouse = other;
        other.spouse = this;
        //@ close PersonInv(other, this);
        //@ close PersonInv(this, other);
        
        
    }
    
    void divorce()
    //@ requires PersonInv(this, ?s) &*& s != null &*& PersonInv(s, this);
    //@ ensures PersonInv(this, null) &*& PersonInv(s, null);
    {
        
        
        //@ open PersonInv(this, ?s0);
        //@ open PersonInv(s0, ?ss);
        spouse.spouse = null;
        spouse = null;
        //@ close PersonInv(s0, null);
        //@ close PersonInv(this, null);
        
        
    }

}

class Program {

    public static void foo(Person a, Person b)
    //@ requires Person.PersonInv(a, ?as) &*& Person.PersonInv(b, ?bs);
    //@ ensures Person.PersonInv(a, as) &*& Person.PersonInv(b, bs);
    {
        Person aSpouse = a.getSpouse();
        Person bSpouse = b.getSpouse();
        if (aSpouse == b) {
            
            //@ assert as == b;
            //@ assert bs == a;
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