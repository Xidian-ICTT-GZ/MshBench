#include "stdlib.h"

struct person
{
  char *name;
  struct person *spouse;
};

/*@ predicate person(struct person *p;) =
      p->name |-> _ &*& p->spouse |-> _; @*/

//@ requires true;
//@ ensures person(result) &*& result->spouse |-> 0;
struct person *create_person()
{
  struct person *p = malloc(sizeof(struct person));
  if (p == 0)
    abort();
  p->spouse = 0;

  return p;
}

//@ requires p->name |-> _ &*& p->spouse |-> _ &*& q->name |-> _ &*& q->spouse |-> _;
//@ ensures p->name |-> _ &*& p->spouse |-> q &*& q->name |-> _ &*& q->spouse |-> p;
void marry(struct person *p, struct person *q)
{
  p->spouse = q;
  q->spouse = p;
}

//@ requires p->name |-> _ &*& p->spouse |-> ?s;
//@ ensures p->name |-> _ &*& p->spouse |-> s &*& result == s;
struct person *person_get_spouse(struct person *p)
{
  return p->spouse;
}

//@ requires p->name |-> _ &*& p->spouse |-> ?q &*& q != 0 &*& q->name |-> _ &*& q->spouse |-> p;
//@ ensures p->name |-> _ &*& p->spouse |-> 0 &*& q->name |-> _ &*& q->spouse |-> 0;
void divorce(struct person *p)
{
  p->spouse->spouse = 0;
  p->spouse = 0;
}

//@ requires person(p);
//@ ensures true;
void die(struct person *p)
{
  if (p->spouse != 0)
  {
    p->spouse->spouse = 0;
  }
  free(p);
}

//@ requires true;
//@ ensures true;
int main()
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