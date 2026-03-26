#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

#include <stdbool.h>

/*@
predicate struct_with_array_pred(struct_with_array *s;) =
  s->x |-> _ &*& s->ar[0..7] |-> _ &*& s->y |-> _;

predicate mystruct_pred(struct mystruct *m;) =
  struct_with_array_pred(&m->s1) &*& m->s2 |-> _;

predicate ar2_pred() = integer_array(&ar2[0], 55, _);

predicate bigArray_pred() = 
  integer(&bigArray[0].x, _) &*& integer_array(&bigArray[0].ar[0], 7, _) &*& integer(&bigArray[0].y, _) &*&
  integer(&bigArray[1].x, _) &*& integer_array(&bigArray[1].ar[0], 7, _) &*& integer(&bigArray[1].y, _) &*&
  integer(&bigArray[2].x, _) &*& integer_array(&bigArray[2].ar[0], 7, _) &*& integer(&bigArray[2].y, _) &*&
  integer(&bigArray[3].x, _) &*& integer_array(&bigArray[3].ar[0], 7, _) &*& integer(&bigArray[3].y, _) &*&
  integer(&bigArray[4].x, _) &*& integer_array(&bigArray[4].ar[0], 7, _) &*& integer(&bigArray[4].y, _) &*&
  integer(&bigArray[5].x, _) &*& integer_array(&bigArray[5].ar[0], 7, _) &*& integer(&bigArray[5].y, _) &*&
  integer(&bigArray[6].x, _) &*& integer_array(&bigArray[6].ar[0], 7, _) &*& integer(&bigArray[6].y, _) &*&
  integer(&bigArray[7].x, _) &*& integer_array(&bigArray[7].ar[0], 7, _) &*& integer(&bigArray[7].y, _) &*&
  integer(&bigArray[8].x, _) &*& integer_array(&bigArray[8].ar[0], 7, _) &*& integer(&bigArray[8].y, _) &*&
  integer(&bigArray[9].x, _) &*& integer_array(&bigArray[9].ar[0], 7, _) &*& integer(&bigArray[9].y, _);

predicate points_pred() = 
  integer(&points[0].x, _) &*& integer(&points[0].y, _) &*&
  integer(&points[1].x, _) &*& integer(&points[1].y, _);

predicate my_global_nested_struct_pred() = mystruct_pred(&my_global_nested_struct);
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
//@ requires y == 17;
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
//@ requires my_global_nested_struct_pred();
//@ ensures my_global_nested_struct_pred();
{
  struct mystruct my_local_nested_struct;

  memset(&my_local_nested_struct, 0, sizeof(struct mystruct));

  memset(&(&my_local_nested_struct)->s1, 0, sizeof(struct_with_array));

  assert(&my_global_nested_struct != &my_local_nested_struct);
  struct mystruct *sh = malloc(sizeof(struct mystruct));
  if (sh == 0)
    abort();
  assert(sh != &my_global_nested_struct);
  assert(sh != &my_local_nested_struct);
  (&(&my_global_nested_struct)->s1)->ar[5] = 100;
  (&(&my_local_nested_struct)->s1)->ar[5] = 200;

  (&sh->s1)->ar[5] = 300;

  free(sh);
}

static int ar2[55];

void mod_ar2(void)
//@ requires ar2_pred();
//@ ensures ar2_pred();
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
//@ requires my_global_nested_struct_pred() &*& bigArray_pred() &*& ar2_pred() &*& points_pred();
//@ ensures my_global_nested_struct_pred() &*& bigArray_pred() &*& ar2_pred() &*& points_pred();
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