#include "stdlib.h"
#include "spouse.h"

/*@
predicate person(struct person* p;)
/*@  p->name |-> ?name &*& p->spouse |-> ?spouse; @*/
@*/

struct person {
  char* name;
  struct person* spouse;
};

struct person *create_person()
  
//@ requires true;
//@ ensures person(result);
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  //@ close person(p);
  p->spouse = 0;
  
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
//@ ensures person(this) &*& (result == 0 || person(result));
{
  //@ open person(this);
  struct person* res = this->spouse;
  //@ if(res != 0) { open person(res); close person(res); }
  //@ close person(this);
  return res;
}

void divorce(struct person* this)
  
//@ requires person(this) &*& this->spouse != 0 &*& person(this->spouse);
//@ ensures person(this) &*& person(this->spouse);
{
  //@ open person(this);
  //@ open person(this->spouse);
  this->spouse->spouse = 0;
  this->spouse = 0;
  //@ close person(this->spouse);
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