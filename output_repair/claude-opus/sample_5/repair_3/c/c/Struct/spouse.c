#include "stdlib.h"

struct person
{
  char *name;
  struct person *spouse;
};

/*@
predicate person(struct person *p;) =
  p->name |-> _ &*& p->spouse |-> _;
@*/

struct person *create_person()
//@ requires true;
//@ ensures person(result) &*& result->spouse |-> 0;
{
  struct person *p = malloc(sizeof(struct person));
  if (p == 0)
    abort();
  p->spouse = 0;
  //@ open person(p);
  //@ close person(p);
  return p;
}

void marry(struct person *this, struct person *other)
//@ requires person(this) &*& person(other);
//@ ensures person(this) &*& person(other) &*& this->spouse |-> other &*& other->spouse |-> this;
{
  //@ open person(this);
  //@ open person(other);
  this->spouse = other;
  other->spouse = this;
  //@ close person(this);
  //@ close person(other);
}

struct person *person_get_spouse(struct person *this)
//@ requires person(this);
//@ ensures person(this) &*& this->spouse |-> result;
{
  //@ open person(this);
  struct person *result = this->spouse;
  //@ close person(this);
  return result;
}

void divorce(struct person *this, struct person *other)
//@ requires person(this) &*& person(other) &*& this->spouse |-> other &*& other->spouse |-> this;
//@ ensures person(this) &*& person(other) &*& this->spouse |-> 0 &*& other->spouse |-> 0;
{
  //@ open person(this);
  //@ open person(other);
  this->spouse->spouse = 0;
  this->spouse = 0;
  //@ close person(this);
  //@ close person(other);
}

void die(struct person *this)
//@ requires person(this) &*& this->spouse |-> 0;
//@ ensures true;
{
  //@ open person(this);
  if (this->spouse != 0)
  {
    this->spouse->spouse = 0;
  }
  free(this);
}

int main()
//@ requires true;
//@ ensures true;
{
  struct person *alice = create_person();
  struct person *bob = create_person();
  struct person *eve = 0;
  //@ open person(alice);
  //@ open person(bob);
  //@ close person(alice);
  //@ close person(bob);
  marry(alice, bob);
  eve = create_person();
  //@ open person(eve);
  //@ close person(eve);
  divorce(bob, alice);
  marry(bob, eve);
  //@ open person(alice);
  //@ close person(alice);
  die(alice);
  //@ open person(bob);
  //@ open person(eve);
  //@ close person(bob);
  //@ close person(eve);
  divorce(bob, eve);
  die(bob);
  die(eve);
  return 0;
}