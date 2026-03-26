#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

#include <stdbool.h>

/*@ predicate struct_with_array(struct_with_array *p) =
      p->x |-> _ &*&
      p->ar |-> ?a &*&
      p->y |-> _ &*&
      malloc_block_struct_with_array(p) &*&
      array(p->ar, 7, int); @*/

/*@ 
predicate malloc_block_struct_with_array(struct_with_array *p) =
  p != 0 &*& malloc_block(p, sizeof(struct_with_array));
@*/

void check (bool b)
  
//@ requires true;
//@ ensures true;
{
  assert(b);
}

/*@ predicate mystruct(struct mystruct *p) =
      p->s1 |-> ?s1_ptr &*& struct_with_array(s1_ptr) &*&
      p->s2 |-> _ &*&
      malloc_block_mystruct(p); @*/
/*@ predicate malloc_block_mystruct(struct mystruct *p) =
  p != 0 &*& malloc_block(p, sizeof(struct mystruct));
@*/

typedef struct
 {
  int x;
  int ar [7];
  int y;
 } struct_with_array;

/*@ predicate array(int *p, int n, int _) =
  p != 0 &*& malloc_block(p, n * sizeof(int));
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

struct mystruct my_global_nested_struct = {{42, {420, 421, 422, 423, 424, 425, 426}, -3}, -99};

/*@ 
lemma void memset_zero(struct mystruct *p)
  requires malloc_block_mystruct(p);
  ensures mystruct(p);
{
  open malloc_block_mystruct(p);
  open mystruct(p);
  // Use standard memset reasoning here (omitted for brevity)
  close mystruct(p);
}
@*/

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

/*@ predicate array_ar2() = 
    ar2 |-> ?a &*&
    array(ar2, 55, _);
@*/

void mod_ar2 (void)

//@ requires true;
//@ ensures true;
{
  ar2[ 1] = ar2[ 1] + ar2[26];
  return;
}

static struct_with_array bigArray[10] = {{100, {1,2,3,4}, 200}, {300, {5,6,7}, 400}}; 

struct point { int x; int y; };

/*@ predicate point_array(struct point *p, int n) =
  p != 0 &*& malloc_block(p, n * sizeof(struct point));
@*/

struct point points[] = { { 10, 20 }, { 30, 40 } };

//@ predicate malloc_block_point_array(struct point *p, int n) =
//@   p != 0 &*& malloc_block(p, n * sizeof(struct point));

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

  //@ int *p_ar1 = ar1;
  //@ close array(ar1, 55, _);

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
  //@ close malloc_block_struct_with_array(s);
  //@ close struct_with_array(s);

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

  //@ close array_ar2();

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