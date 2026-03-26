class Person {

    protected Person spouse;

    //@ predicate Person() = spouse == null;
    //@ predicate Married(Person o) = spouse == o &*& o != null &*& o.spouse == this;

    public  void spouse_symm()
        //@ requires Person();
        //@ ensures Person();
    {
        //@ open Person();
        //@ close Person();
    }

    public Person()
        //@ requires true;
        //@ ensures Person();
    {
        spouse = null;
        //@ close Person();
    }
    
    public Person getSpouse()
        //@ requires Person();
        //@ ensures Person() &*& result == spouse;
    {
        //@ open Person();
        Person s = spouse;
        //@ close Person();
        return s;
    }
    
    protected void setSpouse(Person other)
        //@ requires Person() &*& other != null &*& other.Person();
        //@ ensures Married(other);
    {
        //@ open Person();
        //@ open other.Person();
        spouse = other;
        other.spouse = this;
        //@ close Married(other);
        //@ close other.Married(this);
    }
    
    protected void clearSpouse()
        //@ requires Married(?other);
        //@ ensures Person() &*& other.Person();
    {
        //@ open Married(?other);
        spouse.spouse = null;
        spouse = null;
        //@ close Person();
        //@ close other.Person();
    }
    
    void marry(Person other)
        //@ requires Person() &*& other != null &*& other.Person();
        //@ ensures Married(other);
    {
        other.setSpouse(this);
    }
    
    void divorce()
        //@ requires Married(?other);
        //@ ensures Person() &*& other.Person();
    {
        spouse.clearSpouse();
    }

}

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        Person a = new Person();
        Person b = new Person();
        a.marry(b);
        b.divorce();
    }

}