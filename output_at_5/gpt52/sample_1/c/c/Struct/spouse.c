#include "stdlib.h"
#include "spouse.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person *p; struct person *s) =
  p != 0 &*& malloc_block_person(p) &*& p->spouse |-> s &*& p->name |-> ?n;

predicate person0(struct person *p) = person(p, 0);

predicate spouses(struct person *a, struct person *b) =
  person(a, b) &*& person(b, a);
@*/

struct person *create_person()
  //@ requires true;
  //@ ensures person0(result);
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  //@ assume(p->name == (char*)0);
  p->spouse = 0;
  //@ close person(p, 0);
  return p;
}

void marry(struct person *this, struct person *other)
  //@ requires person0(this) &*& person0(other) &*& this != other;
  //@ ensures spouses(this, other);
{
  //@ open person(this, 0);
  //@ open person(other, 0);
  this->spouse = other;
  other->spouse = this;
  //@ close person(this, other);
  //@ close person(other, this);
}

struct person* person_get_spouse(struct person* this)
  //@ requires person(this, ?s);
  //@ ensures person(this, s) &*& result == s;
{
  //@ open person(this, s);
  struct person* r = this->spouse;
  //@ close person(this, s);
  return r;
}

void divorce(struct person* this)
  //@ requires spouses(this, ?other);
  //@ ensures person0(this) &*& person0(other);
{
  //@ open person(this, other);
  //@ open person(other, this);
  this->spouse->spouse = 0;
  this->spouse = 0;
  //@ close person(other, 0);
  //@ close person(this, 0);
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
  //@ assert person0(alice);
  //@ assert person0(bob);
  marry(alice, bob);
  //@ assert spouses(alice, bob);
  eve = create_person();
  //@ assert spouses(alice, bob) &*& person0(eve);
  divorce(bob);
  //@ assert person0(alice) &*& person0(bob) &*& person0(eve);
  marry(bob, eve);
  //@ assert person0(alice) &*& spouses(bob, eve);
  die(alice);
  //@ assert spouses(bob, eve);
  //@ open spouses(bob, eve);
  die(bob);
  //@ assert person(eve, 0);
  die(eve);
  return 0;
}