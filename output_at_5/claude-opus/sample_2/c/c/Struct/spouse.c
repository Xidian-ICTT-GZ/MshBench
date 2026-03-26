#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person* p;) = p->name |-> _ &*& p->spouse |-> ?s &*& (s == 0 || true);
@*/

struct person *create_person()
  //@ requires true;
  //@ ensures person(result);
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  //@ close person(p);
  return p;
}

void marry(struct person *this, struct person *other)
  //@ requires person(this) &*& person(other);
  //@ ensures person(this) &*& person(other);
{
  //@ open person(this);
  //@ open person(other);
  this->spouse = other;
  other->spouse = this;
  //@ close person(this);
  //@ close person(other);
}

struct person* person_get_spouse(struct person* this)
  //@ requires person(this);
  //@ ensures person(this) &*& (result == 0 ? true : person(result));
{
  //@ open person(this);
  struct person* s = this->spouse;
  //@ close person(this);
  return s;
}

void divorce(struct person* this)
  //@ requires person(this);
  //@ ensures person(this);
{
  //@ open person(this);
  if(this->spouse != 0) {
    //@ open person(this->spouse);
    this->spouse->spouse = 0;
    //@ close person(this->spouse);
  }
  this->spouse = 0;
  //@ close person(this);
}

void die(struct person *this)
  //@ requires person(this);
  //@ ensures true;
{
  //@ open person(this);
  if(this->spouse != 0) {
    //@ open person(this->spouse);
    this->spouse->spouse = 0;
    //@ close person(this->spouse);
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
  die(alice);
  die(bob);
  die(eve);
  return 0;
}