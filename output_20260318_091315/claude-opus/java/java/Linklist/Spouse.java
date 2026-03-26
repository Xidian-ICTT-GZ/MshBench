class Person {

  protected Person spouse;

  /*@
  predicate person_spouse(Person p; Person s) =
    this.spouse |-> s &*&
    (s == null || s.spouse |-> this);
  @*/

  //@ requires person_spouse(this, spouse);
  //@ ensures person_spouse(this, spouse);
  public void spouse_symm()
  {
    //@ open person_spouse(this, spouse);
    //@ open person_spouse(spouse, spouse.spouse);
    //@ close person_spouse(this, spouse);
    //@ close person_spouse(spouse, spouse.spouse);
  }

  public Person()
  //@ ensures person_spouse(this, null);
  {
    spouse = null;
    //@ close person_spouse(this, null);
  }

  //@ requires person_spouse(this, spouse);
  //@ ensures person_spouse(this, spouse) &*& result == spouse;
  public Person getSpouse()
  {
    //@ open person_spouse(this, spouse);
    Person result = spouse;
    //@ close person_spouse(this, spouse);
    return result;
  }

  //@ requires person_spouse(this, spouse) &*& person_spouse(other, other.spouse);
  //@ ensures person_spouse(this, other) &*& person_spouse(other, this);
  protected void setSpouse(Person other)
  {
    //@ open person_spouse(this, spouse);
    //@ open person_spouse(other, other.spouse);
    spouse = other;
    other.spouse = this;
    //@ close person_spouse(this, other);
    //@ close person_spouse(other, this);
  }

  //@ requires person_spouse(this, spouse) &*& spouse != null &*& person_spouse(spouse, this);
  //@ ensures person_spouse(this, null) &*& person_spouse(spouse, null);
  protected void clearSpouse()
  {
    //@ open person_spouse(this, spouse);
    //@ open person_spouse(spouse, this);
    spouse.spouse = null;
    spouse = null;
    //@ close person_spouse(spouse, null);
    //@ close person_spouse(this, null);
  }

  //@ requires person_spouse(this, spouse) &*& person_spouse(other, other.spouse);
  //@ ensures person_spouse(this, other) &*& person_spouse(other, this);
  void marry(Person other)
  {
    other.setSpouse(this);
  }

  //@ requires person_spouse(this, spouse) &*& spouse != null &*& person_spouse(spouse, this);
  //@ ensures person_spouse(this, null) &*& person_spouse(spouse, null);
  void divorce()
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