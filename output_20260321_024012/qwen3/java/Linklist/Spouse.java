class Person {

    protected Person spouse;

    /*@
    predicate_family_instance spouse_inv(Person p) = 
        p.spouse |-> ?s &*& 
        (s == null ? true : 
            s.spouse |-> p &*& 
            spouse_inv(s));
    @*/

    //@ requires this.spouse_inv(this);
    //@ ensures this.spouse_inv(this);
    public  void spouse_symm()
    {
        //@ open spouse_inv(this);
        if (spouse != null) {
            //@ open spouse_inv(spouse);
            //@ assert spouse.spouse == this;
            //@ close spouse_inv(spouse);
        }
        //@ close spouse_inv(this);
    }

    //@ ensures this.spouse_inv(this);
    public Person()
    {
        //@ close spouse_inv(this);
    }
    
    //@ requires this.spouse_inv(this);
    //@ ensures this.spouse_inv(this) &*& result == this.spouse;
    public Person getSpouse()
    {
        return spouse;
    }
    
    //@ requires this.spouse_inv(this) &*& other.spouse_inv(other) &*& this != other;
    //@ ensures this.spouse_inv(this) &*& other.spouse_inv(other);
    protected void setSpouse(Person other)
    {
        //@ open spouse_inv(this);
        //@ open spouse_inv(other);
        spouse = other;
        other.spouse = this;
        //@ close spouse_inv(other);
        //@ close spouse_inv(this);
    }
    
    //@ requires this.spouse_inv(this) &*& this.spouse != null;
    //@ ensures true;
    protected void clearSpouse()
    {
        //@ open spouse_inv(this);
        //@ open spouse_inv(spouse);
        spouse.spouse = null;
        spouse = null;
        //@ close spouse_inv(spouse);
        //@ close spouse_inv(this);
    }
    
    //@ requires this.spouse_inv(this) &*& other.spouse_inv(other) &*& this != other;
    //@ ensures this.spouse_inv(this) &*& other.spouse_inv(other);
    void marry(Person other)
    {
        other.setSpouse(this);
    }
    
    //@ requires this.spouse_inv(this) &*& this.spouse != null;
    //@ ensures true;
    void divorce()
    {
        spouse.clearSpouse();
    }

}

class Program {

    public static void main(String[] args)
    {
        Person a = new Person();
        Person b = new Person();
        a.marry(b);
        b.divorce();
    }

}