#include "stdlib.h"
#include "spouse.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person *p; struct person *s) =
  p != 0 &*& malloc_block_person(p) &*& p->spouse |-> s;

predicate person0(struct person *p) = person(p, _);

predicate persons2(struct person *a, struct person *b) =
  person(a, b) &*& person(b, a);

predicate persons2_divorced(struct person *a, struct person *b) =
  person(a, 0) &*& person(b, 0);

predicate persons3_all(struct person *a, struct person *b, struct person *c) =
  person0(a) &*& person0(b) &*& person0(c);
@*/

struct person *create_person()
  //@ requires true;
  //@ ensures person(result, 0);
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  //@ assume(p != 0);
  p->spouse = 0;
  //@ close person(p, 0);
  return p;
}

void marry(struct person *this, struct person *other)
  //@ requires person(this, 0) &*& person(other, 0);
  //@ ensures persons2(this, other);
{
  //@ open person(this, 0);
  //@ open person(other, 0);
  this->spouse = other;
  other->spouse = this;
  //@ close person(this, other);
  //@ close person(other, this);
}

struct person* person_get_spouse(struct person* this)
  //@ requires person0(this);
  //@ ensures person0(this) &*& result == 0 ? true : true;
{
  //@ open person(this, _);
  struct person* s = this->spouse;
  //@ close person(this, s);
  return s;
}

void divorce(struct person* this)
  //@ requires exists<struct person*>(?other) &*& persons2(this, other);
  //@ ensures persons2_divorced(this, other);
{
  //@ open exists(other);
  //@ open person(this, other);
  //@ open person(other, this);
  this->spouse->spouse = 0;
  this->spouse = 0;
  //@ close person(this, 0);
  //@ close person(other, 0);
}

void die(struct person *this)
  //@ requires person(this, ?s) &*& (s == 0 ? true : person(s, this));
  //@ ensures s == 0 ? true : person(s, 0);
{
  //@ open person(this, s);
  if(this->spouse != 0) {
    //@ open person(s, this);
    this->spouse->spouse = 0;
    //@ close person(s, 0);
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
  //@ close exists(bob);
  marry(alice, bob);
  eve = create_person();
  divorce(bob);
  //@ close exists(eve);
  marry(bob, eve);
  die(alice);
  die(bob);
  die(eve);
  return 0;
}