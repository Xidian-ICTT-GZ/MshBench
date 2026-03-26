#include "stdlib.h"

struct person
{
  char *name;
  struct person *spouse;
};

/*@ predicate person(struct person *p;) =
      p->name |-> _ &*& p->spouse |-> _; @*/

//@ requires true;
//@ ensures person(result) &*& result->spouse |-> 0;
struct person *create_person()
{
  struct person *p = malloc(sizeof(struct person));
  if (p == 0)
    abort();
  p->spouse = 0;

  return p;
}

//@ requires person(this) &*& person(other);
//@ ensures this->name |-> _ &*& this->spouse |-> other &*& other->name |-> _ &*& other->spouse |-> this;
void marry(struct person *this, struct person *other)
{
  this->spouse = other;
  other->spouse = this;
}

//@ requires this->name |-> _ &*& this->spouse |-> ?s;
//@ ensures this->name |-> _ &*& this->spouse |-> s &*& result == s;
struct person *person_get_spouse(struct person *this)
{
  return this->spouse;
}

//@ requires this->name |-> _ &*& this->spouse |-> ?other &*& other != 0 &*& other->name |-> _ &*& other->spouse |-> this;
//@ ensures this->name |-> _ &*& this->spouse |-> 0 &*& other->name |-> _ &*& other->spouse |-> 0;
void divorce(struct person *this)
{
  this->spouse->spouse = 0;
  this->spouse = 0;
}

//@ requires person(this);
//@ ensures true;
void die(struct person *this)
{
  if (this->spouse != 0)
  {
    this->spouse->spouse = 0;
  }
  free(this);
}

//@ requires true;
//@ ensures true;
int main()
{
  struct person *alice = create_person();
  struct person *bob = create_person();
  struct person *eve = 0;
  //@ open person(alice);
  //@ open person(bob);
  marry(alice, bob);
  eve = create_person();
  //@ open person(eve);
  divorce(bob);
  //@ close person(alice);
  //@ close person(bob);
  marry(bob, eve);
  //@ close person(alice);
  die(alice);
  //@ close person(bob);
  die(bob);
  //@ close person(eve);
  die(eve);
  return 0;
}