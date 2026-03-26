/*@ 
predicate Person_spouse(Person p; Person spouse) =
    p.spouse |-> spouse;
@*/

class Person {

    protected Person spouse;

    //@ requires true;
    //@ ensures true;
    public void spouse_symm()
    {
    }

    //@ requires true;
    //@ ensures Person_spouse(this, null);
    public Person()
    {
        //@ close Person_spouse(this, null);
    }
    
    //@ requires Person_spouse(this, ?s);
    //@ ensures Person_spouse(this, s) &*& result == s;
    public Person getSpouse()
    {
        return spouse;
    }
    
    //@ requires Person_spouse(this, _) &*& Person_spouse(other, _);
    //@ ensures Person_spouse(this, other) &*& Person_spouse(other, this);
    protected void setSpouse(Person other)
    {
        //@ open Person_spouse(this, _);
        //@ open Person_spouse(other, _);
        spouse = other;
        other.spouse = this;
        //@ close Person_spouse(this, other);
        //@ close Person_spouse(other, this);
    }
    
    //@ requires Person_spouse(this, ?s) &*& s != null &*& Person_spouse(s, this);
    //@ ensures Person_spouse(this, null) &*& Person_spouse(s, null);
    protected void clearSpouse()
    {
        //@ open Person_spouse(this, s);
        //@ open Person_spouse(s, this);
        spouse.spouse = null;
        spouse = null;
        //@ close Person_spouse(this, null);
        //@ close Person_spouse(s, null);
    }
    
    //@ requires Person_spouse(this, _) &*& Person_spouse(other, _);
    //@ ensures Person_spouse(this, other) &*& Person_spouse(other, this);
    void marry(Person other)
    {
        other.setSpouse(this);
    }
    
    //@ requires Person_spouse(this, ?s) &*& s != null &*& Person_spouse(s, this);
    //@ ensures Person_spouse(this, null) &*& Person_spouse(s, null);
    void divorce()
    {
        spouse.clearSpouse();
    }

}

class Program {

    //@ requires true;
    //@ ensures true;
    public static void main(String[] args)
    {
        Person a = new Person();
        Person b = new Person();
        a.marry(b);
        b.divorce();
    }

}