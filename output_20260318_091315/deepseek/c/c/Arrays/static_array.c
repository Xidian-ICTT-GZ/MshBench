#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

#include <stdbool.h>

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

/*@
predicate struct_with_array(struct_with_array *s;) =
  s->x |-> ?x &*&
  integer(&s->ar[0], 7) &*&
  s->y |-> ?y;
@*/

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

/*@
predicate mystruct(struct mystruct *s;) =
  struct_with_array(&s->s1) &*&
  s->s2 |-> ?s2;
@*/

struct mystruct my_global_nested_struct = {{42, {420, 421, 422, 423, 424, 425, 426}, -3}, -99};

/*@
predicate my_global_nested_struct() =
  mystruct(&my_global_nested_struct);
@*/

static void foo()
  
  //@ requires my_global_nested_struct();
  //@ ensures my_global_nested_struct();
{
  struct mystruct my_local_nested_struct;
  
  memset(&my_local_nested_struct, 0, sizeof(struct mystruct));
  
  
  
  memset(&(&my_local_nested_struct)->s1, 0, sizeof(struct_with_array));
  
  
  
  
  assert(&my_global_nested_struct != &my_local_nested_struct);
  struct mystruct *sh = malloc(sizeof(struct mystruct));
  if (sh == 0) abort();
  //@ open my_global_nested_struct();
  //@ close mystruct(sh);
  assert(sh != &my_global_nested_struct);
  assert(sh != &my_local_nested_struct);
  (&(&my_global_nested_struct)->s1)->ar[5] = 100;
  (&(&my_local_nested_struct)->s1)->ar[5] = 200;
  
  (&sh->s1)->ar[5] = 300;
  
  //@ open mystruct(sh);
  free(sh);
  //@ close my_global_nested_struct();
}

static int ar2 [55];

/*@
predicate ar2() = integer(&ar2[0], 55);
@*/

void mod_ar2 (void)

  //@ requires ar2();
  //@ ensures ar2();
 {
  ar2[ 1] = ar2[ 1] + ar2[26];
  return;
 }

static struct_with_array bigArray[10] = {{100, {1,2,3,4}, 200}, {300, {5,6,7}, 400}}; 

/*@
predicate bigArray() = integer(&bigArray[0].x, 10 * (2 + 7 + 1));
@*/

struct point { int x; int y; };

struct point points[] = { { 10, 20 }, { 30, 40 } };

/*@
predicate points() = integer(&points[0].x, 4);
@*/

int main(int argc, char **argv) 

  //@ requires true;
  //@ ensures true;
 {
  
  //@ open my_global_nested_struct();
  //@ open mystruct(&my_global_nested_struct);
  //@ open struct_with_array(&(&my_global_nested_struct)->s1);
  check((&(&my_global_nested_struct)->s1)->x == 42);
  check((&(&my_global_nested_struct)->s1)->ar[0] == 420);
  check((&(&my_global_nested_struct)->s1)->ar[6] == 426);
  check((&(&my_global_nested_struct)->s1)->y == -3);
  check((&my_global_nested_struct)->s2 == -99);
  //@ close struct_with_array(&(&my_global_nested_struct)->s1);
  //@ close mystruct(&my_global_nested_struct);
  //@ close my_global_nested_struct();
  
  struct_with_array *bigArrayPtr = bigArray;
  //@ open bigArray();
  check((bigArrayPtr + 1)->x == 300);
  check((bigArrayPtr + 1)->ar[2] == 7);
  //@ close bigArray();
  
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
  //@ close struct_with_array(s);

  
  //@ open struct_with_array(s);
  s->ar[ 0] = 1;
  
  s->ar[ 1] = 5;
  
  s->ar[ 2] = 0;
  
  s->ar[ 6] = 2;
  s->ar[ 1] = s->ar[ 1] + s->ar[ 6];
  //@ close struct_with_array(s);

  //@ open struct_with_array(s);
  if (s->ar[i] == 7)
   { t += s->ar[2]; }
   else
   { assert false; }
  //@ close struct_with_array(s);

  //@ open struct_with_array(s);
  assert (s->ar[0] == 1);
  //@ close struct_with_array(s);

  
  
  
  
  
  //@ open struct_with_array(s);
  free (s);

  
  
  
  //@ open ar2();
  check(ar2[0] == 0);
  ar2[ 0] = 1;
  ar2[ 1] = 5;
  ar2[ 2] = 0;
  ar2[26] = 2;
  //@ close ar2();
  mod_ar2 ();

  //@ open ar2();
  if (ar2[i] == 7)
   { t += ar2[2]; }
   else
   { assert false; }
  //@ close ar2();

  //@ open ar2();
  assert (ar2[1] == 7);
  //@ close ar2();

  //@ open points();
  assert (points[1].y == 40);
  //@ close points();
  
  
  
  
  

  
  
  
  
  
  
  
  
  
  
  int xs[] = {1, 2, 3}, ys[] = {4, 5, 6, 7};
  xs[1] = xs[2];
  assert (xs[1] == 3);
  ys[2] = ys[3];
  assert (ys[2] == 7);

  return (t);
 }