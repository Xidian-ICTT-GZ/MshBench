#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

#include <stdbool.h>

/*@ predicate struct_with_array_pred(struct_with_array *p; int x_val, int ar0, int ar1, int ar2,
                                        int ar3, int ar4, int ar5, int ar6, int y_val) =
      p->x |-> x_val &*&
      p->ar[0] |-> ar0 &*& p->ar[1] |-> ar1 &*& p->ar[2] |-> ar2 &*& p->ar[3] |-> ar3 &*&
      p->ar[4] |-> ar4 &*& p->ar[5] |-> ar5 &*& p->ar[6] |-> ar6 &*&
      p->y |-> y_val;
@*/

void check (bool b)
  
//@ requires true;
//@ ensures true;
{
  assert(b);
}

typedef struct
 {
  int x;
  int ar [7];
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

struct mystruct {
  struct_with_array s1;
  int s2;
};

/*@ predicate mystruct_pred(struct mystruct *p; int x_val, int ar0, int ar1, int ar2, int ar3, int ar4,
                           int ar5, int ar6, int y_val, int s2_val) =
      struct_with_array_pred(&p->s1, x_val, ar0, ar1, ar2, ar3, ar4, ar5, ar6, y_val) &*&
      p->s2 |-> s2_val;
@*/

struct mystruct my_global_nested_struct = {{42, {420, 421, 422, 423, 424, 425, 426}, -3}, -99};

static void foo()
  
//@ requires true;
//@ ensures true;
{
  struct mystruct my_local_nested_struct;
  
  memset(&my_local_nested_struct, 0, sizeof(struct mystruct));
  
  memset(&(&my_local_nested_struct)->s1, 0, sizeof(struct_with_array));
  
  assert(&my_global_nested_struct != &my_local_nested_struct);
  struct mystruct *sh = malloc(sizeof(struct mystruct));
  if (sh == 0) abort();
  assert(sh != &my_global_nested_struct);
  assert(sh != &my_local_nested_struct);
  (&(&my_global_nested_struct)->s1)->ar[5] = 100;
  (&(&my_local_nested_struct)->s1)->ar[5] = 200;
  
  (&sh->s1)->ar[5] = 300;
  
  
  free(sh);
}

static int ar2 [55];

/*@ predicate ar2_pred(int *p, int len) =
      len == 0 ?
        true
      :
        p |-> _ &*& ar2_pred(p + 1, len - 1);
@*/

void mod_ar2 (void)

//@ requires ar2 + 55 |-> _ &*& ar2 + 1 |-> ?v1 &*& ar2 + 26 |-> ?v26;
//@ ensures ar2 + 1 |-> v1 + v26;
{
  ar2[ 1] = ar2[ 1] + ar2[26];
  return;
}

static struct_with_array bigArray[10] = {{100, {1,2,3,4}, 200}, {300, {5,6,7}, 400}};

/*@ predicate point_pred(struct point *p; int x_val, int y_val) =
      p->x |-> x_val &*& p->y |-> y_val;
@*/

struct point { int x; int y; };

struct point points[] = { { 10, 20 }, { 30, 40 } };

int main(int argc, char **argv) 
//@ requires true;
//@ ensures true;
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
  int    i = 1;
  int    ar1 [55];
  int    t;

  ar1[ 0] = 1;
  ar1[ 1] = 5;
  ar1[ 2] = 0;
  ar1[26] = 2;
  ar1[ 1] = ar1[ 1] + ar1[26];

  //@ close struct_with_array_pred(s, _, _, _, _, _, _, _, _); // Preparation for malloc, but we do it below

  if (ar1[i] == 7)
   { t = ar1[2]; }
   else
   { assert false; }

  assert (ar1[26] == 2);

  s = malloc (sizeof (struct_with_array));
  if (s == 0) { abort(); }

  //@ close struct_with_array_pred(s, 0, 0, 0, 0, 0, 0, 0, 0);
  
  s->ar[ 0] = 1;
  s->ar[ 1] = 5;
  s->ar[ 2] = 0;
  s->ar[ 6] = 2;
  s->ar[ 1] = s->ar[ 1] + s->ar[ 6];

  if (s->ar[i] == 7)
   { t += s->ar[2]; }
   else
   { assert false; }

  assert (s->ar[0] == 1);

  free (s);

  check(ar2[0] == 0);
  ar2[ 0] = 1;
  ar2[ 1] = 5;
  ar2[ 2] = 0;
  ar2[26] = 2;
  mod_ar2 ();

  if (ar2[i] == 7)
   { t += ar2[2]; }
   else
   { assert false; }

  assert (ar2[1] == 7);

  assert (points[1].y == 40);

  int xs[] = {1, 2, 3}, ys[] = {4, 5, 6, 7};
  xs[1] = xs[2];
  assert (xs[1] == 3);
  ys[2] = ys[3];
  assert (ys[2] == 7);

  return (t);
}