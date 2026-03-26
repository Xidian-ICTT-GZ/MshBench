#include "stdlib.h"
#include "spouse.h"

struct person
{
  char *name;
  struct person *spouse;
};

/*@
predicate person(struct person *p; struct person *s) =
  p->name |-> ?n &*& p->spouse |-> s &*& malloc_block_person(p);

predicate single(struct person *p) =
  person(p, 0);

predicate married(struct person *p, struct person *q) =
  person(p, q) &*& person(q, p) &*& p != 0 &*& q != 0;
@*/

struct person *create_person()
//@ requires true;
//@ ensures single(result);
{
  struct person *p = malloc(sizeof(struct person));
  if (p == 0)
    abort();
  p->spouse = 0;
  //@ close person(p, 0);
  //@ close single(p);
  return p;
}

void marry(struct person *this, struct person *other)
//@ requires single(this) &*& single(other) &*& this != other;
//@ ensures married(this, other);
{
  //@ open single(this);
  //@ open single(other);
  //@ open person(this, 0);
  //@ open person(other, 0);
  this->spouse = other;
  other->spouse = this;
  //@ close person(this, other);
  //@ close person(other, this);
  //@ close married(this, other);
}

struct person *person_get_spouse(struct person *this)
//@ requires person(this, ?s);
//@ ensures person(this, s) &*& result == s;
{
  //@ open person(this, s);
  //@ close person(this, s);
  return this->spouse;
}

void divorce(struct person *this)
//@ requires married(this, ?other);
//@ ensures single(this) &*& single(other);
{
  //@ open married(this, other);
  //@ open person(this, other);
  //@ open person(other, this);
  this->spouse->spouse = 0;
  this->spouse = 0;
  //@ close person(this, 0);
  //@ close person(other, 0);
  //@ close single(this);
  //@ close single(other);
}

void die(struct person *this)
//@ requires single(this) || married(this, ?other);
//@ ensures single(this) ? true : single(other);
{
  //@ if (this->spouse == 0) { open single(this); open person(this, 0); } else { open married(this, ?s); open person(this, s); open person(s, this); }
  if (this->spouse != 0)
  {
    this->spouse->spouse = 0;
    //@ close person(this->spouse, 0);
    //@ close single(this->spouse);
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