#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

#include <stdbool.h>

/*@
predicate struct_with_arrayp(struct_with_array *s) =
  s->x |-> _ &*& ints(s->ar, 7, _) &*& s->y |-> _;

predicate mystructp(struct mystruct *m) =
  struct_with_arrayp(&m->s1) &*& m->s2 |-> _;

predicate globals() =
  mystructp(&my_global_nested_struct) &*& ints(ar2, 55, _) &*&
  struct_with_arrayp(&bigArray[0]) &*& struct_with_arrayp(&bigArray[1]) &*& struct_with_arrayp(&bigArray[2]) &*& struct_with_arrayp(&bigArray[3]) &*& struct_with_arrayp(&bigArray[4]) &*&
  struct_with_arrayp(&bigArray[5]) &*& struct_with_arrayp(&bigArray[6]) &*& struct_with_arrayp(&bigArray[7]) &*& struct_with_arrayp(&bigArray[8]) &*& struct_with_arrayp(&bigArray[9]) &*&
  ints((int*)points, 2 * sizeof(struct point) / sizeof(int), _);
@*/

void check (bool b)
  //@ requires b == true;
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

struct mystruct my_global_nested_struct = {{42, {420, 421, 422, 423, 424, 425, 426}, -3}, -99};

static void foo()
  //@ requires globals();
  //@ ensures globals();
  
  
{
  struct mystruct my_local_nested_struct;
  
  memset(&my_local_nested_struct, 0, sizeof(struct mystruct));
  //@ close mystructp(&my_local_nested_struct);
  
  
  
  memset(&(&my_local_nested_struct)->s1, 0, sizeof(struct_with_array));
  
  
  
  
  assert(&my_global_nested_struct != &my_local_nested_struct);
  struct mystruct *sh = malloc(sizeof(struct mystruct));
  if (sh == 0) abort();
  //@ close mystructp(sh);
  assert(sh != &my_global_nested_struct);
  assert(sh != &my_local_nested_struct);
  //@ open globals();
  //@ open mystructp(&my_global_nested_struct);
  //@ open struct_with_arrayp(&my_global_nested_struct.s1);
  (&(&my_global_nested_struct)->s1)->ar[5] = 100;
  //@ close struct_with_arrayp(&my_global_nested_struct.s1);
  //@ close mystructp(&my_global_nested_struct);
  //@ close globals();
  //@ open mystructp(&my_local_nested_struct);
  //@ open struct_with_arrayp(&my_local_nested_struct.s1);
  (&(&my_local_nested_struct)->s1)->ar[5] = 200;
  //@ close struct_with_arrayp(&my_local_nested_struct.s1);
  //@ close mystructp(&my_local_nested_struct);
  
  //@ open mystructp(sh);
  //@ open struct_with_arrayp(&sh->s1);
  (&sh->s1)->ar[5] = 300;
  //@ close struct_with_arrayp(&sh->s1);
  //@ close mystructp(sh);
  
  
  //@ open mystructp(sh);
  //@ open struct_with_arrayp(&sh->s1);
  free(sh);
  //@ open mystructp(&my_local_nested_struct);
  //@ open struct_with_arrayp(&my_local_nested_struct.s1);
  //@ close struct_with_arrayp(&my_local_nested_struct.s1);
  //@ close mystructp(&my_local_nested_struct);
}

static int ar2 [55];

void mod_ar2 (void)
  //@ requires globals();
  //@ ensures globals();

 {
  //@ open globals();
  //@ open ints(ar2, 55, ?vs);
  ar2[ 1] = ar2[ 1] + ar2[26];
  //@ close ints(ar2, 55, _);
  //@ close globals();
  return;
 }

static struct_with_array bigArray[10] = {{100, {1,2,3,4}, 200}, {300, {5,6,7}, 400}}; 

struct point { int x; int y; };

struct point points[] = { { 10, 20 }, { 30, 40 } };

int main(int argc, char **argv) 
  //@ requires true;
  //@ ensures true;

 {
  
  //@ close mystructp(&my_global_nested_struct);
  //@ close ints(ar2, 55, _);
  //@ close struct_with_arrayp(&bigArray[0]);
  //@ close struct_with_arrayp(&bigArray[1]);
  //@ close struct_with_arrayp(&bigArray[2]);
  //@ close struct_with_arrayp(&bigArray[3]);
  //@ close struct_with_arrayp(&bigArray[4]);
  //@ close struct_with_arrayp(&bigArray[5]);
  //@ close struct_with_arrayp(&bigArray[6]);
  //@ close struct_with_arrayp(&bigArray[7]);
  //@ close struct_with_arrayp(&bigArray[8]);
  //@ close struct_with_arrayp(&bigArray[9]);
  //@ close ints((int*)points, 2 * sizeof(struct point) / sizeof(int), _);
  //@ close globals();
  
  //@ open globals();
  //@ open mystructp(&my_global_nested_struct);
  //@ open struct_with_arrayp(&my_global_nested_struct.s1);
  check((&(&my_global_nested_struct)->s1)->x == 42);
  check((&(&my_global_nested_struct)->s1)->ar[0] == 420);
  check((&(&my_global_nested_struct)->s1)->ar[6] == 426);
  check((&(&my_global_nested_struct)->s1)->y == -3);
  //@ close struct_with_arrayp(&my_global_nested_struct.s1);
  check((&my_global_nested_struct)->s2 == -99);
  //@ close mystructp(&my_global_nested_struct);
  
  struct_with_array *bigArrayPtr = bigArray;
  check((bigArrayPtr + 1)->x == 300);
  check((bigArrayPtr + 1)->ar[2] == 7);
  //@ close globals();
  
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

  if (ar1[i] == 7)
   { t = ar1[2]; }
   else
   { assert false; }

  assert (ar1[26] == 2);
  
  
  
  
  
  

  
  s = malloc (sizeof (struct_with_array));
  if (s == 0) { abort(); }

  
  //@ close struct_with_arrayp(s);

  
  //@ open struct_with_arrayp(s);
  s->ar[ 0] = 1;
  
  s->ar[ 1] = 5;
  
  s->ar[ 2] = 0;
  
  s->ar[ 6] = 2;
  s->ar[ 1] = s->ar[ 1] + s->ar[ 6];
  //@ close struct_with_arrayp(s);

  //@ open struct_with_arrayp(s);
  if (s->ar[i] == 7)
   { t += s->ar[2]; }
   else
   { assert false; }

  assert (s->ar[0] == 1);
  //@ close struct_with_arrayp(s);

  
  
  
  
  
  //@ open struct_with_arrayp(s);
  free (s);

  
  
  
  //@ open globals();
  //@ open ints(ar2, 55, ?ar2vs);
  check(ar2[0] == 0);
  ar2[ 0] = 1;
  ar2[ 1] = 5;
  ar2[ 2] = 0;
  ar2[26] = 2;
  //@ close ints(ar2, 55, _);
  //@ close globals();
  mod_ar2 ();
  //@ open globals();
  //@ open ints(ar2, 55, ?ar2vs2);

  if (ar2[i] == 7)
   { t += ar2[2]; }
   else
   { assert false; }

  assert (ar2[1] == 7);

  //@ close ints(ar2, 55, _);

  assert (points[1].y == 40);
  
  
  
  
  

  
  
  
  
  
  
  
  
  
  
  int xs[] = {1, 2, 3}, ys[] = {4, 5, 6, 7};
  xs[1] = xs[2];
  assert (xs[1] == 3);
  ys[2] = ys[3];
  assert (ys[2] == 7);

  //@ close globals();
  //@ open globals();
  return (t);
 }