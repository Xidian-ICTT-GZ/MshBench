class Person {

    protected Person spouse;
    
    //@ predicate Person() = spouse == null;
    //@ predicate Married(Person other) = spouse == other &*& other != null &*& other.spouse == this;

    public  void spouse_symm()
        //@ requires Person();
        //@ ensures Person();
    {
        //@ close Person();
    }

    public Person()
        //@ ensures Person();
    {
        //@ close Person();
    }
    
    public Person getSpouse()
        //@ requires Person();
        //@ ensures Person() &*& result == null;
    {
        //@ open Person();
        return spouse;
        //@ close Person();
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