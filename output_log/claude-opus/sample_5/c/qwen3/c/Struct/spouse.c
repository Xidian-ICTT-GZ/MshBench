#include "stdlib.h"
#include "spouse.h"

/*@ predicate person(struct person *p; char *name, struct person *spouse) =
    p != 0 &*& 
    malloc_block_person(p) &*&
    p->name |-> name &*&
    p->spouse |-> spouse;
@*/

/*@ predicate persons(struct person *p, struct person *q; char *name_p, char *name_q) =
    p != 0 &*& q != 0 &*&
    person(p, name_p, q) &*&
    person(q, name_q, p);
@*/

struct person
{
  char *name;
  struct person *spouse;
};

struct person *create_person()

/*@ requires true;
    ensures person(result, 0, 0);
@*/
{
  struct person *p = malloc(sizeof(struct person));
  if (p == 0)
    abort();
  //@ assume p != 0;
  //@ malloc_block_person(p);
  p->spouse = 0;
  //@ assert p->spouse |-> 0;
  //@ close person(p, 0, 0);
  return p;
}

/*@ requires person(this, ?name_this, ?spouse_this) &*& person(other, ?name_other, ?spouse_other);
    ensures person(this, name_this, other) &*& person(other, name_other, this);
@*/
void marry(struct person *this, struct person *other)

{
  //@ open person(this, name_this, spouse_this);
  //@ open person(other, name_other, spouse_other);
  this->spouse = other;
  other->spouse = this;
  //@ close person(this, name_this, other);
  //@ close person(other, name_other, this);
}

/*@ requires person(this, ?name, ?spouse);
    ensures person(this, name, spouse) &*& result == spouse;
@*/
struct person *person_get_spouse(struct person *this)

{
  //@ open person(this, name, spouse);
  struct person *res = this->spouse;
  //@ close person(this, name, spouse);
  return res;
}

/*@ requires person(this, ?name, ?spouse) &*& spouse != 0 &*& person(spouse, ?name_spouse, this);
    ensures person(this, name, 0) &*& person(spouse, name_spouse, 0);
@*/
void divorce(struct person *this)

{
  //@ open person(this, name, spouse);
  //@ open person(spouse, name_spouse, this);
  this->spouse->spouse = 0;
  this->spouse = 0;
  //@ close person(this, name, 0);
  //@ close person(spouse, name_spouse, 0);
}

/*@ requires person(this, ?name, ?spouse) &*& (spouse == 0 || person(spouse, ?name_spouse, this));
    ensures true;
@*/
void die(struct person *this)

{
  //@ open person(this, name, spouse);
  if (this->spouse != 0)
  {
    //@ open person(this->spouse, name_spouse, this);
    this->spouse->spouse = 0;
    //@ close person(this->spouse, name_spouse, 0);
  }
  free(this);
  //@ leak malloc_block_person(this);
}

int main()

/*@ requires true;
    ensures true;
@*/
{
  struct person *alice = create_person();
  struct person *bob = create_person();
  struct person *eve = 0;
  marry(alice, bob);
  eve = create_person();
  divorce(bob);
  marry(bob, eve);
  die(alice);
  die(bob);
  die(eve);
  return 0;
}