#include "stdlib.h"
#include "spouse.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@ predicate person(struct person *p; struct person *s) =
      p->name |-> _ &*& p->spouse |-> s; @*/

struct person *create_person()
  //@ requires true;
  //@ ensures person(result, 0);
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  //@ close person(p, 0);
  return p;
}

void marry(struct person *this, struct person *other)
  //@ requires person(this, ?s1) &*& person(other, ?s2);
  //@ ensures person(this, other) &*& person(other, this);
{
  //@ open person(this, s1);
  //@ open person(other, s2);
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
  struct person* result = this->spouse;
  //@ close person(this, s);
  return result;
}

void divorce(struct person* this)
  //@ requires person(this, ?s) &*& s != 0 &*& person(s, this);
  //@ ensures person(this, 0) &*& person(s, 0);
{
  //@ open person(this, s);
  //@ open person(s, this);
  s->spouse = 0;
  this->spouse = 0;
  //@ close person(this, 0);
  //@ close person(s, 0);
}

void die(struct person *this)
  //@ requires person(this, ?s);
  //@ ensures true;
{
  //@ open person(this, s);
  if(this->spouse != 0) {
    struct person* sp = this->spouse;
    //@ open person(sp, this);
    sp->spouse = 0;
    //@ close person(sp, 0);
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