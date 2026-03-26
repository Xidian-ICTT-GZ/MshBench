#include "stdlib.h"

struct person
{
  char *name;
  struct person *spouse;
};

/*@ predicate person(struct person *p) = p->name |-> _ &*& p->spouse |-> _; @*/

/*@ predicate married(struct person *p, struct person *q) = 
  person(p) &*& person(q) &*& p->spouse |-> q &*& q->spouse |-> p; @*/

/*@ predicate single(struct person *p) = 
  person(p) &*& p->spouse |-> 0; @*/

struct person *create_person()
//@ requires true;
//@ ensures single(result);
{
  struct person *p = malloc(sizeof(struct person));
  if (p == 0)
    abort();
  p->spouse = 0;

  return p;
}

void marry(struct person *this, struct person *other)
//@ requires single(this) &*& single(other);
//@ ensures married(this, other);
{
  this->spouse = other;
  other->spouse = this;
}

struct person *person_get_spouse(struct person *this)
//@ requires person(this);
//@ ensures this->spouse |-> result;
{
  return this->spouse;
}

void divorce(struct person *this)
//@ requires married(this, ?other);
//@ ensures single(this) &*& single(other);
{
  this->spouse->spouse = 0;
  this->spouse = 0;
}

void die(struct person *this)
//@ requires person(this);
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