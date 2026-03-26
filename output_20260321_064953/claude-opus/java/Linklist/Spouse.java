class Person {

    protected Person spouse;

    /*@
    predicate person() = this.spouse |-> ?s &*& (s == null || s.spouse |-> this);
    @*/

    //@ requires person();
    //@ ensures person();
    public void spouse_symm()
    {
        //@ open person();
        //@ if (spouse != null) { 
        //@   open spouse.person();
        //@   assert spouse.spouse == this;
        //@   close spouse.person();
        //@ }
        //@ close person();
    }

    //@ requires true;
    //@ ensures person();
    public Person()
    {
        //@ this.spouse = null;
        //@ close person();
    }

    //@ requires person();
    //@ ensures person() &*& result == spouse;
    public Person getSpouse()
    {
        //@ open person();
        Person result = spouse;
        //@ close person();
        return result;
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
    //@ ensures person() &*& (spouse == null ? true : spouse.person());
    protected void clearSpouse()
    {
        //@ open person();
        //@ open spouse.person();
        spouse.spouse = null;
        spouse = null;
        //@ close person();
    }

    //@ requires person() &*& other.person();
    //@ ensures person() &*& other.person();
    void marry(Person other)
    {
        //@ open person();
        //@ open other.person();
        other.setSpouse(this);
        //@ close other.person();
        //@ close person();
    }

    //@ requires person() &*& spouse != null &*& spouse.person();
    //@ ensures person();
    void divorce()
    {
        //@ open person();
        //@ open spouse.person();
        spouse.clearSpouse();
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