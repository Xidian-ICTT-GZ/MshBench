class Person {

/*@
  predicate person(this) = this.spouse |-> ?s &*& (s == null || person(s));
@*/

    protected Person spouse;

/*@
  // We assume the person predicate holds after constructor
  // and after setSpouse/clearSpouse appropriately update ownership.
@*/

    public Person()
        //@ requires true;
        //@ ensures person(this);
    {
        spouse = null;
    }

    public Person getSpouse()
        //@ requires person(this);
        //@ ensures person(this) &*& person(result);
    {
        return spouse;
    }

    protected void setSpouse(Person other)
        //@ requires person(this) &*& person(other);
        //@ ensures person(this) &*& person(other) &*& spouse == other &*& other.spouse == this;
    {
        spouse = other;
        other.spouse = this;
    }

    protected void clearSpouse()
        //@ requires person(this) &*& spouse != null &*& person(spouse);
        //@ ensures person(this) &*& (spouse == null);
    {
        spouse.spouse = null;
        spouse = null;
    }

    void marry(Person other)
        //@ requires person(this) &*& person(other);
        //@ ensures person(this) &*& person(other) &*& spouse == other &*& other.spouse == this;
    {
        other.setSpouse(this);
    }

    void divorce()
        //@ requires person(this) &*& spouse != null &*& person(spouse);
        //@ ensures person(this) &*& spouse == null;
    {
        spouse.clearSpouse();
    }

    public void spouse_symm()
        //@ requires person(this) &*& spouse != null &*& person(spouse);
        //@ ensures person(this) &*& person(spouse);
    {
        //@ assert spouse.spouse == this; // by setSpouse contract
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