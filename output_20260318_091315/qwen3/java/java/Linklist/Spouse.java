/*@ predicate spouse_of(Person p, Person s) = p.spouse |-> s; @*/

class Person {

protected Person spouse;

//@ requires true;
//@ ensures true;
public void spouse_symm()
{
}

//@ requires true;
//@ ensures spouse_of(this, null);
public Person()
{
}

//@ requires spouse_of(this, ?s);
//@ ensures result == s;
public Person getSpouse()
{
    return spouse;
}

/*@ 
lemma void setSpouse_lemma(Person this, Person other)
    requires [?f1]spouse_of(this, ?s1) &*& [?f2]spouse_of(other, ?s2);
    ensures [f1]spouse_of(this, other) &*& [f2]spouse_of(other, this);
@*/
//@ requires [?f1]spouse_of(this, ?s1) &*& [?f2]spouse_of(other, ?s2);
//@ ensures [f1]spouse_of(this, other) &*& [f2]spouse_of(other, this);
protected void setSpouse(Person other)
{
    spouse = other;
    other.spouse = this;
}

/*@ 
lemma void clearSpouse_lemma(Person this)
    requires spouse_of(this, ?s) &*& spouse_of(s, this);
    ensures spouse_of(this, null) &*& spouse_of(s, null);
@*/
//@ requires spouse_of(this, ?s) &*& spouse_of(s, this);
//@ ensures spouse_of(this, null) &*& spouse_of(s, null);
protected void clearSpouse()
{
    spouse.spouse = null;
    spouse = null;
}

//@ requires [?f1]spouse_of(this, null) &*& [?f2]spouse_of(other, null);
//@ ensures [f1]spouse_of(this, other) &*& [f2]spouse_of(other, this);
void marry(Person other)
{
    other.setSpouse(this);
}

//@ requires spouse_of(this, ?s) &*& spouse_of(s, this);
//@ ensures spouse_of(this, null) &*& spouse_of(s, null);
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