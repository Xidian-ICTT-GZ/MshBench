class Person {

/*@
  predicate inv(Person this) = this.spouse |-> ?s &*& (s == null || s.spouse == this);
@*/

    protected Person spouse;

    public void spouse_symm()
    //@ requires inv(this);
    //@ ensures inv(this);
    {
        //@ open inv(this);
        //@ if (spouse != null) { open inv(spouse); }
        //@ if (spouse != null) { assert spouse.spouse == this; }
        //@ if (spouse != null) { close inv(spouse); }
        //@ close inv(this);
    }

    public Person()
    //@ requires true;
    //@ ensures inv(this);
    {
        //@ close inv(this);
    }

    public Person getSpouse()
    //@ requires inv(this);
    //@ ensures inv(this) &*& result == this.spouse;
    {
        //@ open inv(this);
        Person r = spouse;
        //@ close inv(this);
        return r;
    }

    protected void setSpouse(Person other)
    //@ requires inv(this) &*& inv(other);
    //@ ensures inv(this) &*& inv(other);
    {
        //@ open inv(this);
        //@ open inv(other);
        spouse = other;
        other.spouse = this;
        //@ close inv(other);
        //@ close inv(this);
    }

    protected void clearSpouse()
    //@ requires inv(this);
    //@ ensures inv(this);
    {
        //@ open inv(this);
        if (spouse != null) {
            //@ open inv(spouse);
            spouse.spouse = null;
            //@ close inv(spouse);
        }
        spouse = null;
        //@ close inv(this);
    }

    void marry(Person other)
    //@ requires inv(this) &*& inv(other);
    //@ ensures inv(this) &*& inv(other) &*& this.spouse == other &*& other.spouse == this;
    {
        other.setSpouse(this);
    }

    void divorce()
    //@ requires inv(this);
    //@ ensures inv(this);
    {
        //@ open inv(this);
        if (spouse != null) {
            spouse.clearSpouse();
        }
        //@ close inv(this);
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