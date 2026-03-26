#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

#include <stdbool.h>

/*@

predicate struct_with_array_(struct_with_array *s) =
  s->x |-> ?x &*&
  s->ar[0] |-> ?a0 &*& s->ar[1] |-> ?a1 &*& s->ar[2] |-> ?a2 &*& s->ar[3] |-> ?a3 &*& s->ar[4] |-> ?a4 &*& s->ar[5] |-> ?a5 &*& s->ar[6] |-> ?a6 &*&
  s->y |-> ?y;

predicate mystruct_(struct mystruct *m) =
  struct_with_array_(&m->s1) &*&
  m->s2 |-> ?s2;

predicate ints(int *p; int count) =
  count <= 0 ? emp : p[0] |-> _ &*& ints(p+1; count-1);

predicate chars(char *p; int count) =
  count <= 0 ? emp : p[0] |-> _ &*& chars(p+1; count-1);

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
  //@ close struct_with_array_(&foo);
  //@ close struct_with_array_(&bar);
  //@ close chars(buf, 3);
  
  check((&foo)->x == 123);
  check((&foo)->ar[6] == 17);
  check(buf[1] == 2);
  //@ open struct_with_array_(&foo);
  //@ open struct_with_array_(&bar);
  //@ open chars(buf, 3);
}

struct mystruct {
  struct_with_array s1;
  int s2;
};

struct mystruct my_global_nested_struct = {{42, {420, 421, 422, 423, 424, 425, 426}, -3}, -99};

static void foo()
  //@ requires mystruct_(&my_global_nested_struct);
  //@ ensures mystruct_(&my_global_nested_struct);
  
{
  struct mystruct my_local_nested_struct;
  //@ close mystruct_(&my_local_nested_struct);
  //@ open mystruct_(&my_local_nested_struct);
  
  memset(&my_local_nested_struct, 0, sizeof(struct mystruct));
  //@ close mystruct_(&my_local_nested_struct);
  //@ open mystruct_(&my_local_nested_struct);
  
  
  
  memset(&(&my_local_nested_struct)->s1, 0, sizeof(struct_with_array));
  //@ close struct_with_array_(&(&my_local_nested_struct)->s1);
  
  
  
  
  assert(&my_global_nested_struct != &my_local_nested_struct);
  struct mystruct *sh = malloc(sizeof(struct mystruct));
  if (sh == 0) abort();
  //@ close mystruct_(sh);
  assert(sh != &my_global_nested_struct);
  assert(sh != &my_local_nested_struct);
  //@ open mystruct_(&my_global_nested_struct);
  (&(&my_global_nested_struct)->s1)->ar[5] = 100;
  //@ close mystruct_(&my_global_nested_struct);
  //@ open mystruct_(&my_local_nested_struct);
  (&(&my_local_nested_struct)->s1)->ar[5] = 200;
  //@ close mystruct_(&my_local_nested_struct);
  
  //@ open mystruct_(sh);
  (&sh->s1)->ar[5] = 300;
  //@ close mystruct_(sh);
  
  
  //@ open mystruct_(sh);
  free(sh);
  //@ open mystruct_(&my_local_nested_struct);
}

static int ar2 [55];

void mod_ar2 (void)
  //@ requires ints(ar2, 55);
  //@ ensures ints(ar2, 55);

 {
  ar2[ 1] = ar2[ 1] + ar2[26];
  return;
 }

static struct_with_array bigArray[10] = {{100, {1,2,3,4}, 200}, {300, {5,6,7}, 400}}; 

struct point { int x; int y; };

struct point points[] = { { 10, 20 }, { 30, 40 } };

int main(int argc, char **argv) 
  //@ requires true;
  //@ ensures true;

 {
  //@ close ints(ar2, 55);
  //@ close struct_with_array_(&bigArray[0]);
  //@ close struct_with_array_(&bigArray[1]);
  //@ close struct_with_array_(&bigArray[2]);
  //@ close struct_with_array_(&bigArray[3]);
  //@ close struct_with_array_(&bigArray[4]);
  //@ close struct_with_array_(&bigArray[5]);
  //@ close struct_with_array_(&bigArray[6]);
  //@ close struct_with_array_(&bigArray[7]);
  //@ close struct_with_array_(&bigArray[8]);
  //@ close struct_with_array_(&bigArray[9]);
  //@ close mystruct_(&my_global_nested_struct);
  
  //@ open mystruct_(&my_global_nested_struct);
  check((&(&my_global_nested_struct)->s1)->x == 42);
  check((&(&my_global_nested_struct)->s1)->ar[0] == 420);
  check((&(&my_global_nested_struct)->s1)->ar[6] == 426);
  check((&(&my_global_nested_struct)->s1)->y == -3);
  check((&my_global_nested_struct)->s2 == -99);
  //@ close mystruct_(&my_global_nested_struct);
  
  struct_with_array *bigArrayPtr = bigArray;
  //@ open struct_with_array_(&bigArray[1]);
  check((bigArrayPtr + 1)->x == 300);
  check((bigArrayPtr + 1)->ar[2] == 7);
  //@ close struct_with_array_(&bigArray[1]);
  
  foo();

  struct_with_array *s;
  int    i = 1;
  int    ar1 [55];
  int    t;
  //@ close ints(ar1, 55);

  
  
  ar1[ 0] = 1;
  
  ar1[ 1] = 5;
  
  ar1[ 2] = 0;
  
  ar1[26] = 2;
  ar1[ 1] = ar1[ 1] + ar1[26];

  if (ar1[i] == 7)
   { t = ar1[2]; }
   else
   { assert false; }

  assert (ar1[26] == 2);
  
  
  
  
  
  

  
  s = malloc (sizeof (struct_with_array));
  if (s == 0) { abort(); }
  //@ close struct_with_array_(s);
  //@ open struct_with_array_(s);

  
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

  
  
  
  
  
  //@ close struct_with_array_(s);
  //@ open struct_with_array_(s);
  free (s);

  
  
  
  //@ open ints(ar2, 55);
  check(ar2[0] == 0);
  ar2[ 0] = 1;
  ar2[ 1] = 5;
  ar2[ 2] = 0;
  ar2[26] = 2;
  //@ close ints(ar2, 55);
  mod_ar2 ();
  //@ open ints(ar2, 55);

  if (ar2[i] == 7)
   { t += ar2[2]; }
   else
   { assert false; }

  assert (ar2[1] == 7);

  assert (points[1].y == 40);
  
  
  
  
  

  
  
  
  
  
  
  
  
  
  
  int xs[] = {1, 2, 3}, ys[] = {4, 5, 6, 7};
  //@ close ints(xs, 3);
  //@ close ints(ys, 4);
  xs[1] = xs[2];
  assert (xs[1] == 3);
  ys[2] = ys[3];
  assert (ys[2] == 7);
  //@ open ints(xs, 3);
  //@ open ints(ys, 4);
  //@ open ints(ar2, 55);
  //@ open mystruct_(&my_global_nested_struct);
  //@ open struct_with_array_(&bigArray[0]);
  //@ open struct_with_array_(&bigArray[1]);
  //@ open struct_with_array_(&bigArray[2]);
  //@ open struct_with_array_(&bigArray[3]);
  //@ open struct_with_array_(&bigArray[4]);
  //@ open struct_with_array_(&bigArray[5]);
  //@ open struct_with_array_(&bigArray[6]);
  //@ open struct_with_array_(&bigArray[7]);
  //@ open struct_with_array_(&bigArray[8]);
  //@ open struct_with_array_(&bigArray[9]);
  //@ open ints(ar1, 55);

  return (t);
 }