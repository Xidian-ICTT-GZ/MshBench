final class Person {

private Person spouse;

/*@
predicate valid() =
    this.spouse |-> ?s
    &*& (s == null ? true : s.spouse |-> this);
@*/

/*@
predicate married() =
    this.spouse |-> ?s
    &*& s != null
    &*& s.spouse |-> this;
@*/

/*@
predicate single() =
    this.spouse |-> null;
@*/

public Person()
    //@ requires true;
    //@ ensures single();
{
    //@ close single();
}

public Person getSpouse()
    //@ requires valid();
    //@ ensures valid() &*& result == null ? single() : married();
{
    //@ open valid();
    return spouse;
    //@ close valid();
}

void marry(Person other)
    //@ requires single() &*& other != null &*& other.single();
    //@ ensures married() &*& other.married();
{
    //@ open single();
    //@ open other.single();
    spouse = other;
    other.spouse = this;
    //@ close married();
    //@ close other.married();
}

void divorce()
    //@ requires married();
    //@ ensures single();
{
    //@ open married();
    spouse.spouse = null;
    spouse = null;
    //@ close single();
}

}

class Program {

public static void foo(Person a, Person b)
    //@ requires a.valid() &*& b.valid();
    //@ ensures a.valid() &*& b.valid();
{
    //@ open a.valid();
    Person aSpouse = a.getSpouse();
    //@ open b.valid();
    Person bSpouse = b.getSpouse();
    if (aSpouse == b) {
        //@ assert bSpouse == a;
    }
    //@ close a.valid();
    //@ close b.valid();
}

public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
{
    Person a = new Person();
    Person b = new Person();
    a.marry(b);
    foo(a, b);
    b.divorce();
}

}