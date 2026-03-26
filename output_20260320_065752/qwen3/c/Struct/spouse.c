#include "stdlib.h"
#include "spouse.h"

/*@ predicate person(struct person* p; struct person* spouse) =
  p != 0 &*&
  malloc_block_person(p) &*&
  p->spouse |-> spouse;
@*/

struct person {
  char* name;
  struct person* spouse;
};

//@ requires true;
//@ ensures person(result, 0);
struct person *create_person()
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  //@ close person(p, 0);
  return p;
}

//@ requires person(this, _) &*& person(other, _);
//@ ensures person(this, other) &*& person(other, this);
void marry(struct person *this, struct person *other)
{
  //@ open person(this, _);
  //@ open person(other, _);
  this->spouse = other;
  other->spouse = this;
  //@ close person(this, other);
  //@ close person(other, this);
}

//@ requires person(this, ?s);
//@ ensures person(this, s) &*& result == s;
struct person* person_get_spouse(struct person* this)
{
  //@ open person(this, ?s);
  struct person* sp = this->spouse;
  //@ close person(this, s);
  return sp;
}

//@ requires person(this, ?s) &*& s != 0 &*& person(s, this);
//@ ensures person(this, 0) &*& person(s, 0);
void divorce(struct person* this)
{
  //@ open person(this, ?s);
  //@ open person(s, this);
  this->spouse->spouse = 0;
  this->spouse = 0;
  //@ close person(this, 0);
  //@ close person(s, 0);
}

//@ requires person(this, ?s) &*& (s != 0 ? person(s, this) : true);
//@ ensures true;
void die(struct person *this)
{
  //@ open person(this, ?s);
  if(this->spouse != 0) {
    //@ open person(s, this);
    this->spouse->spouse = 0;
    //@ close person(s, 0);
  }
  free(this); 
}

//@ requires true;
//@ ensures true;
int main() 
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