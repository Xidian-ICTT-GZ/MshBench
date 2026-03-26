#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

#include <stdbool.h>

/*@

predicate struct_with_array_(struct_with_array *p; int x, int a0, int a1, int a2, int a3, int a4, int a5, int a6, int y) =
  p->x |-> x &*&
  p->ar[0] |-> a0 &*& p->ar[1] |-> a1 &*& p->ar[2] |-> a2 &*& p->ar[3] |-> a3 &*& p->ar[4] |-> a4 &*& p->ar[5] |-> a5 &*& p->ar[6] |-> a6 &*&
  p->y |-> y;

predicate mystruct_(struct mystruct *p; int s1x, int s1a0, int s1a1, int s1a2, int s1a3, int s1a4, int s1a5, int s1a6, int s1y, int s2) =
  struct_with_array_(&p->s1; s1x, s1a0, s1a1, s1a2, s1a3, s1a4, s1a5, s1a6, s1y) &*&
  p->s2 |-> s2;

@*/

void check(bool b)
//@ requires true;
//@ ensures true;
{
  assert(b);
}

typedef struct
{
  int x;
  int ar[7];
  int y;
} struct_with_array;

void check_local_inits(int x, int y)
//@ requires true;
//@ ensures true;
{
  struct_with_array foo = {123, {2, x, 5, 7, 11, 13, y}, 456};
  struct_with_array bar = foo;
  char buf[3] = {1, 2, 3};

  check((&foo)->x == 123);
  check((&foo)->ar[6] == 17);
  check(buf[1] == 2);
}

struct mystruct
{
  struct_with_array s1;
  int s2;
};

struct mystruct my_global_nested_struct = {{42, {420, 421, 422, 423, 424, 425, 426}, -3}, -99};

static void foo()
//@ requires mystruct_(&my_global_nested_struct; 42, 420, 421, 422, 423, 424, 425, 426, -3, -99);
//@ ensures mystruct_(&my_global_nested_struct; 42, 420, 421, 422, 423, 424, 100, 426, -3, -99);
{
  struct mystruct my_local_nested_struct;

  memset(&my_local_nested_struct, 0, sizeof(struct mystruct));
  //@ open mystruct_(&my_global_nested_struct; 42, 420, 421, 422, 423, 424, 425, 426, -3, -99);

  memset(&(&my_local_nested_struct)->s1, 0, sizeof(struct_with_array));

  assert(&my_global_nested_struct != &my_local_nested_struct);
  struct mystruct *sh = malloc(sizeof(struct mystruct));
  if (sh == 0)
    abort();
  //@ close mystruct_(sh; _, _, _, _, _, _, _, _, _, _);
  assert(sh != &my_global_nested_struct);
  assert(sh != &my_local_nested_struct);
  (&(&my_global_nested_struct)->s1)->ar[5] = 100;
  (&(&my_local_nested_struct)->s1)->ar[5] = 200;

  (&sh->s1)->ar[5] = 300;

  //@ open mystruct_(sh; _, _, _, _, _, _, _, _, _, _);
  free(sh);
  //@ close mystruct_(&my_global_nested_struct; 42, 420, 421, 422, 423, 424, 100, 426, -3, -99);
}

static int ar2[55];

void mod_ar2(void)
//@ requires ar2[1] |-> ?v1 &*& ar2[26] |-> ?v26;
//@ ensures ar2[1] |-> (v1 + v26) &*& ar2[26] |-> v26;
{
  ar2[1] = ar2[1] + ar2[26];
  return;
}

static struct_with_array bigArray[10] = {{100, {1, 2, 3, 4}, 200}, {300, {5, 6, 7}, 400}};

struct point
{
  int x;
  int y;
};

struct point points[] = {{10, 20}, {30, 40}};

int main(int argc, char **argv)
//@ requires mystruct_(&my_global_nested_struct; 42, 420, 421, 422, 423, 424, 425, 426, -3, -99) &*& ar2[0..55] |-> ?vs &*& points[0..2] |-> ?ps &*& bigArray[0..10] |-> ?bas;
//@ ensures mystruct_(&my_global_nested_struct; 42, 420, 421, 422, 423, 424, 100, 426, -3, -99) &*& ar2[0..55] |-> _ &*& points[0..2] |-> ps &*& bigArray[0..10] |-> bas;
{

  check((&(&my_global_nested_struct)->s1)->x == 42);
  check((&(&my_global_nested_struct)->s1)->ar[0] == 420);
  check((&(&my_global_nested_struct)->s1)->ar[6] == 426);
  check((&(&my_global_nested_struct)->s1)->y == -3);
  check((&my_global_nested_struct)->s2 == -99);

  struct_with_array *bigArrayPtr = bigArray;
  check((bigArrayPtr + 1)->x == 300);
  check((bigArrayPtr + 1)->ar[2] == 7);

  foo();

  struct_with_array *s;
  int i = 1;
  int ar1[55];
  int t;

  ar1[0] = 1;

  ar1[1] = 5;

  ar1[2] = 0;

  ar1[26] = 2;
  ar1[1] = ar1[1] + ar1[26];

  if (ar1[i] == 7)
  {
    t = ar1[2];
  }
  else
  {
    assert false;
  }

  assert(ar1[26] == 2);

  s = malloc(sizeof(struct_with_array));
  if (s == 0)
  {
    abort();
  }
  //@ close struct_with_array_(s; _, _, _, _, _, _, _, _, _);

  s->ar[0] = 1;

  s->ar[1] = 5;

  s->ar[2] = 0;

  s->ar[6] = 2;
  s->ar[1] = s->ar[1] + s->ar[6];

  if (s->ar[i] == 7)
  {
    t += s->ar[2];
  }
  else
  {
    assert false;
  }

  assert(s->ar[0] == 1);

  //@ open struct_with_array_(s; _, _, _, _, _, _, _, _, _);
  free(s);

  check(ar2[0] == 0);
  ar2[0] = 1;
  ar2[1] = 5;
  ar2[2] = 0;
  ar2[26] = 2;
  mod_ar2();

  if (ar2[i] == 7)
  {
    t += ar2[2];
  }
  else
  {
    assert false;
  }

  assert(ar2[1] == 7);

  assert(points[1].y == 40);

  int xs[] = {1, 2, 3}, ys[] = {4, 5, 6, 7};
  xs[1] = xs[2];
  assert(xs[1] == 3);
  ys[2] = ys[3];
  assert(ys[2] == 7);

  return (t);
}