#include "stdlib.h"

struct person
{
  char *name;
  struct person *spouse;
};

/*@ predicate person(struct person *p;) = 
      p->name |-> _ &*& p->spouse |-> _; @*/

struct person *create_person()
//@ requires true;
//@ ensures person(result) &*& result->spouse |-> 0;
{
  struct person *p = malloc(sizeof(struct person));
  if (p == 0)
    abort();
  p->spouse = 0;

  return p;
}

void marry(struct person *this, struct person *other)
//@ requires person(this) &*& person(other);
//@ ensures person(this) &*& person(other) &*& this->spouse |-> other &*& other->spouse |-> this;
{
  this->spouse = other;
  other->spouse = this;
}

struct person *person_get_spouse(struct person *this)
//@ requires this->spouse |-> ?s;
//@ ensures this->spouse |-> s &*& result == s;
{
  return this->spouse;
}

void divorce(struct person *this)
//@ requires person(this) &*& this->spouse |-> ?other &*& other != 0 &*& person(other) &*& other->spouse |-> this;
//@ ensures person(this) &*& this->spouse |-> 0 &*& person(other) &*& other->spouse |-> 0;
{
  this->spouse->spouse = 0;
  this->spouse = 0;
}

void die(struct person *this)
//@ requires person(this) &*& this->spouse |-> 0;
//@ ensures true;
{
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
  marry(alice, bob);
  eve = create_person();
  divorce(bob);
  marry(bob, eve);
  die(alice);
  die(bob);
  die(eve);
  return 0;
}