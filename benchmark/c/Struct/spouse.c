#include "stdlib.h"
#include "spouse.h"

struct person {
  char* name;
  struct person* spouse;
};






struct person *create_person()
  
  
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  
  return p;
}

void marry(struct person *this, struct person *other)
  
  
{
  
  
  this->spouse = other;
  other->spouse = this;
  
  
}

struct person* person_get_spouse(struct person* this)
  
  
{
  
  return this->spouse;
  
}

void divorce(struct person* this)
  
  
{
  
  
  this->spouse->spouse = 0;
  this->spouse = 0;
  
  
}































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