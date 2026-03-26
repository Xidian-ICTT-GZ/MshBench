class Person {

    protected Person spouse;

    /*@
    predicate person() = this.spouse |-> _;
    @*/

    //@ requires true;
    //@ ensures person();
    public Person()
    {
        //@ close person();
    }

    //@ requires person();
    //@ ensures person() &*& result == spouse;
    public Person getSpouse()
    {
        //@ open person();
        Person s = spouse;
        //@ close person();
        return s;
    }

    //@ requires person() &*& other.person();
    //@ ensures person() &*& other.person();
    protected void setSpouse(Person other)
    {
        //@ open person();
        //@ open other.person();
        spouse = other;
        other.spouse = this;
        //@ close other.person();
        //@ close person();
    }

    //@ requires person() &*& spouse != null &*& spouse.person();
    //@ ensures person();
    protected void clearSpouse()
    {
        //@ open person();
        //@ open spouse.person();
        spouse.spouse = null;
        //@ close spouse.person();
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
    //@ ensures person();
    void divorce()
    {
        spouse.clearSpouse();
    }

    //@ requires person();
    //@ ensures person();
    public void spouse_symm()
    {
        //@ open person();
        //@ close person();
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