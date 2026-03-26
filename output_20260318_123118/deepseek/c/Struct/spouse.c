#include "stdlib.h"
#include "spouse.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person* p;) =
  p->name |-> _ &*& p->spouse |-> ?sp &*& malloc_block_person(p);
@*/

/*@
predicate married(struct person* p, struct person* q;) =
  p->spouse |-> q &*& q->spouse |-> p &*& malloc_block_person(p) &*& malloc_block_person(q);
@*/

/*@
predicate single(struct person* p;) =
  p->spouse |-> 0 &*& malloc_block_person(p);
@*/

struct person *create_person()
  //@ requires true;
  //@ ensures single(result);
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  //@ close single(p);
  return p;
}

void marry(struct person *this, struct person *other)
  //@ requires single(this) &*& single(other);
  //@ ensures married(this, other);
{
  //@ open single(this);
  //@ open single(other);
  this->spouse = other;
  other->spouse = this;
  //@ close married(this, other);
}

struct person* person_get_spouse(struct person* this)
  //@ requires person(this);
  //@ ensures person(this) &*& result == this->spouse;
{
  //@ open person(this);
  struct person* sp = this->spouse;
  //@ close person(this);
  return sp;
}

void divorce(struct person* this)
  //@ requires married(this, ?other);
  //@ ensures single(this) &*& single(other);
{
  //@ open married(this, other);
  this->spouse->spouse = 0;
  this->spouse = 0;
  //@ close single(this);
  //@ close single(other);
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