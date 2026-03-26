#include "stdlib.h"
#include "spouse.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person *p;) =
  p->name |-> _ &*& p->spouse |-> ?s &*&
  (s == 0 ? true : s->spouse |-> p);
@*/

/*@
predicate person_single(struct person *p;) =
  p->name |-> _ &*& p->spouse |-> 0;
@*/

struct person *create_person()
  //@ requires true;
  //@ ensures person_single(result);
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  //@ close person_single(p);
  return p;
}

void marry(struct person *this, struct person *other)
  //@ requires person_single(this) &*& person_single(other) &*& this != other;
  //@ ensures person(this) &*& this->spouse |-> other;
{
  //@ open person_single(this);
  //@ open person_single(other);
  this->spouse = other;
  other->spouse = this;
  //@ close person(this);
}

struct person* person_get_spouse(struct person* this)
  //@ requires this->spouse |-> ?s;
  //@ ensures this->spouse |-> s &*& result == s;
{
  return this->spouse;
}

void divorce(struct person* this)
  //@ requires person(this) &*& this->spouse |-> ?other &*& other != 0;
  //@ ensures person_single(this) &*& person_single(other);
{
  //@ open person(this);
  this->spouse->spouse = 0;
  //@ close person_single(this->spouse);
  this->spouse = 0;
  //@ close person_single(this);
}

void die(struct person *this)
  //@ requires person_single(this) &*& (this->spouse |-> 0 ? true : true);
  //@ ensures true;
{
  //@ open person_single(this);
  if(this->spouse != 0) {
    this->spouse->spouse = 0;
  }
  free(this); 
}

int main() 
  //@ requires true;
  //@ ensures true;
{
  struct person* alice = create_person();
  struct person* bob = create_person();
  struct person* eve = 0;
  marry(alice, bob);
  eve = create_person();
  divorce(bob);
  marry(bob, eve);
  //@ open person(alice);
  die(alice);
  //@ open person(bob);
  die(bob);
  die(eve);
  return 0;
}