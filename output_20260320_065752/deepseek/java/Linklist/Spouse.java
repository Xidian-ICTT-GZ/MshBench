class Person {

    protected Person spouse;

    /*@
    predicate Person() = spouse |-> ?s;
    @*/

    //@ requires true;
    //@ ensures Person();
    public  void spouse_symm()
        //@ requires Person();
        //@ ensures Person();
    {
        //@ open Person();
        //@ close Person();
    }

    //@ ensures Person();
    public Person()
        //@ ensures Person();
    {
        //@ close Person();
    }
    
    //@ requires Person();
    //@ ensures Person() &*& result == spouse;
    public Person getSpouse()
        //@ requires Person();
        //@ ensures Person() &*& result == spouse;
    {
        //@ open Person();
        //@ close Person();
        return spouse;
    }
    
    //@ requires Person() &*& other != null &*& other.Person();
    //@ ensures Person() &*& other.Person();
    protected void setSpouse(Person other)
        //@ requires Person() &*& other != null &*& other.Person();
        //@ ensures Person() &*& other.Person();
    {
        //@ open Person();
        //@ open other.Person();
        spouse = other;
        other.spouse = this;
        //@ close other.Person();
        //@ close Person();
    }
    
    //@ requires Person() &*& spouse != null &*& spouse.Person();
    //@ ensures Person();
    protected void clearSpouse()
        //@ requires Person() &*& spouse != null &*& spouse.Person();
        //@ ensures Person();
    {
        //@ open Person();
        //@ open spouse.Person();
        spouse.spouse = null;
        spouse = null;
        //@ close Person();
    }
    
    //@ requires Person() &*& other != null &*& other.Person();
    //@ ensures Person() &*& other.Person();
    void marry(Person other)
        //@ requires Person() &*& other != null &*& other.Person();
        //@ ensures Person() &*& other.Person();
    {
        other.setSpouse(this);
    }
    
    //@ requires Person() &*& spouse != null &*& spouse.Person();
    //@ ensures Person();
    void divorce()
        //@ requires Person() &*& spouse != null &*& spouse.Person();
        //@ ensures Person();
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