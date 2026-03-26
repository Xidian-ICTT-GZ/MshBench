class Person {

    protected Person spouse;

    /*@
    predicate person() = this.spouse |-> _;
    @*/

    //@ requires person();
    //@ ensures person();
    public void spouse_symm()
    {
    }

    //@ requires true;
    //@ ensures person();
    public Person()
    {
    }
    
    //@ requires person();
    //@ ensures person() &*& result == spouse;
    public Person getSpouse()
    {
        return spouse;
    }
    
    //@ requires person() &*& other.person();
    //@ ensures person() &*& other.person();
    protected void setSpouse(Person other)
    {
        //@ open person();
        spouse = other;
        other.spouse = this;
        //@ close person();
        //@ close other.person();
    }
    
    //@ requires person() &*& spouse != null &*& spouse.person();
    //@ ensures person() &*& (spouse == null ? true : spouse.person());
    protected void clearSpouse()
    {
        //@ open person();
        spouse.spouse = null;
        spouse = null;
        //@ close person();
    }
    
    //@ requires person() &*& other.person();
    //@ ensures person() &*& other.person();
    void marry(Person other)
    {
        other.setSpouse(this);
    }
    
    //@ requires person() &*& spouse != null &*& spouse.person();
    //@ ensures person() &*& (spouse == null ? true : spouse.person());
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