#include "stdlib.h"
#include "spouse.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person *p; struct person *s) =
  p != 0 &*& malloc_block_person(p) &*& p->name |-> _ &*& p->spouse |-> s;
@*/

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
  //@ requires person(this, 0) &*& person(other, 0) &*& this != other;
  //@ ensures person(this, other) &*& person(other, this);
  
  
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
  
  struct person* res = this->spouse;
  
  //@ close person(this, s);
  return res;
  
}

void divorce(struct person* this)
  //@ requires person(this, ?other) &*& other != 0 &*& person(other, this);
  //@ ensures person(this, 0) &*& person(other, 0);
  
  
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
  marry(alice, bob);
  eve = create_person();
  divorce(bob);
  marry(bob, eve);
  die(alice);
  //@ open person(bob, eve);
  //@ open person(eve, bob);
  die(bob);
  //@ open person(eve, 0);
  die(eve);
  return 0;
}