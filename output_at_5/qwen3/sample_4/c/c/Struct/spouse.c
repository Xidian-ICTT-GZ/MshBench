#include "stdlib.h"

//@ predicate person(struct person *p) = p != 0 &*& \valid(p) &*& \valid_read(p->name) &*& \valid_read(p->spouse);
//@ predicate married(struct person *a, struct person *b) = a != 0 &*& b != 0 &*& a->spouse == b &*& b->spouse == a;

struct person {
  char* name;
  struct person* spouse;
};

//@ requires true;
//@ ensures \result == 0 || person(\result);
struct person *create_person()
  
  
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  
  return p;
}

//@ requires person(this) &*& person(other);
//@ ensures married(this, other);
void marry(struct person *this, struct person *other)
  
  
{
  
  
  this->spouse = other;
  other->spouse = this;
  
  
}

//@ requires person(this);
//@ ensures \result == this->spouse;
struct person* person_get_spouse(struct person* this)
  
  
{
  
  return this->spouse;
  
}

//@ requires person(this) &*& this->spouse != 0 &*& married(this, this->spouse);
//@ ensures person(this) &*& this->spouse == 0;
void divorce(struct person* this)
  
  
{
  
  
  this->spouse->spouse = 0;
  this->spouse = 0;
  
  
}

//@ requires person(this);
//@ ensures true;
void die(struct person *this)
  
  
{
  
  if(this->spouse != 0) {
    
    this->spouse->spouse = 0;
    
  }
  free(this); 
}

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