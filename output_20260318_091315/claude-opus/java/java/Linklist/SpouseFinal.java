final class Person {

  private Person spouse;

  /*@ 
    predicate person(Person p; Person spouse) =
      p.spouse |-> spouse &*&
      (spouse == null || spouse.spouse == p);
  @*/

  //@ requires true;
  //@ ensures person(this, null);
  public Person()
  {
  }
  
  //@ requires person(this, ?sp);
  //@ ensures person(this, sp) &*& result == sp;
  public Person getSpouse()
  {
    return spouse;
  }
  
  //@ requires person(this, null) &*& person(other, null);
  //@ ensures  person(this, other) &*& person(other, this);
  void marry(Person other)
  {
    spouse = other;
    other.spouse = this;
  }
  
  //@ requires person(this, ?sp) &*& sp != null &*& person(sp, this);
  //@ ensures person(this, null) &*& person(sp, null);
  void divorce()
  {
    spouse.spouse = null;
    spouse = null;
  }

}

class Program {

  //@ requires person(a, ?aSp) &*& person(b, ?bSp);
  //@ ensures person(a, aSp) &*& person(b, bSp);
  public static void foo(Person a, Person b)
  {
    Person aSpouse = a.getSpouse();
    Person bSpouse = b.getSpouse();
    if (aSpouse == b) {
      assert bSpouse == a;
    }
  }

  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
  {
    Person a = new Person();
    Person b = new Person();
    a.marry(b);
    foo(a, b);
    b.divorce();
  }

}