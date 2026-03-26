#include "stdlib.h"
#include "spouse.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@ 
predicate person(struct person* p; pointer var) = 
  p != 0 &*& malloc_block_person(p) &*& p->name |-> _ &*& p->spouse |-> ?s &*& 
  (s == 0 || (s != 0 &*& s->spouse |-> p));
@*/

struct person *create_person()
  //@ requires true;
  //@ ensures person(result, _);
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  //@ p->name = 0;
  p->spouse = 0;
  
  return p;
}

void marry(struct person *this, struct person *other)
  //@ requires person(this, _) &*& person(other, _);
  //@ ensures person(this, _) &*& person(other, _) &*& this->spouse == other &*& other->spouse == this;
{
  this->spouse = other;
  other->spouse = this;
}

struct person* person_get_spouse(struct person* this)
  //@ requires person(this, _);
  //@ ensures person(this, _) &*& result == this->spouse;
{
  return this->spouse;
}

void divorce(struct person* this)
  //@ requires person(this, _);
  //@ ensures person(this, _) &*& this->spouse == 0;
{
  //@ struct person* s = this->spouse;
  this->spouse->spouse = 0;
  this->spouse = 0;
}

void die(struct person *this)
  //@ requires person(this, _);
  //@ ensures true;
{
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
  die(alice);
  die(bob);
  die(eve);
  return 0;
}