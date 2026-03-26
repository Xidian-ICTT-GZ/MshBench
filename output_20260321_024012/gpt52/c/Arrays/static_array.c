#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

#include <stdbool.h>

/*@
predicate malloc_block_struct_with_array(struct_with_array *p) =
    malloc_block(p, sizeof(struct_with_array));

predicate struct_with_array_pred(struct_with_array *p) =
    p->x |-> _ &*& p->ar[..7] |-> _ &*& p->y |-> _;

predicate malloc_block_mystruct(struct mystruct *p) =
    malloc_block(p, sizeof(struct mystruct));

predicate mystruct_pred(struct mystruct *p) =
    struct_with_array_pred(&p->s1) &*& p->s2 |-> _;
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

struct mystruct my_global_nested_struct = {{42, {420, 421, 422, 423, 424, 425, 426}, -3}, -99};

static void foo()
  //@ requires mystruct_pred(&my_global_nested_struct);
  //@ ensures mystruct_pred(&my_global_nested_struct);
  
  
{
  struct mystruct my_local_nested_struct;
  //@ close mystruct_pred(&my_local_nested_struct);
  
  //@ open mystruct_pred(&my_local_nested_struct);
  memset(&my_local_nested_struct, 0, sizeof(struct mystruct));
  //@ close mystruct_pred(&my_local_nested_struct);
  
  
  
  //@ open mystruct_pred(&my_local_nested_struct);
  //@ open struct_with_array_pred(&my_local_nested_struct.s1);
  memset(&(&my_local_nested_struct)->s1, 0, sizeof(struct_with_array));
  //@ close struct_with_array_pred(&my_local_nested_struct.s1);
  //@ close mystruct_pred(&my_local_nested_struct);
  
  
  
  
  assert(&my_global_nested_struct != &my_local_nested_struct);
  struct mystruct *sh = malloc(sizeof(struct mystruct));
  if (sh == 0) abort();
  //@ close mystruct_pred(sh);
  //@ close malloc_block_mystruct(sh);
  assert(sh != &my_global_nested_struct);
  assert(sh != &my_local_nested_struct);
  //@ open mystruct_pred(&my_global_nested_struct);
  //@ open struct_with_array_pred(&my_global_nested_struct.s1);
  (&(&my_global_nested_struct)->s1)->ar[5] = 100;
  //@ close struct_with_array_pred(&my_global_nested_struct.s1);
  //@ close mystruct_pred(&my_global_nested_struct);
  //@ open mystruct_pred(&my_local_nested_struct);
  //@ open struct_with_array_pred(&my_local_nested_struct.s1);
  (&(&my_local_nested_struct)->s1)->ar[5] = 200;
  //@ close struct_with_array_pred(&my_local_nested_struct.s1);
  //@ close mystruct_pred(&my_local_nested_struct);
  
  //@ open mystruct_pred(sh);
  //@ open struct_with_array_pred(&sh->s1);
  (&sh->s1)->ar[5] = 300;
  //@ close struct_with_array_pred(&sh->s1);
  //@ close mystruct_pred(sh);
  
  
  //@ open malloc_block_mystruct(sh);
  //@ open mystruct_pred(sh);
  free(sh);
}

static int ar2 [55];

void mod_ar2 (void)
  //@ requires ar2[..55] |-> _;
  //@ ensures ar2[..55] |-> _;

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
  //@ close mystruct_pred(&my_global_nested_struct);
  //@ close ar2[..55] |-> _;
  //@ close bigArray[..10] |-> _;
  //@ close points[..2] |-> _;
  
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

  if (ar1[i] == 7)
   { t = ar1[2]; }
   else
   { assert false; }

  assert (ar1[26] == 2);
  
  
  
  
  
  

  
  s = malloc (sizeof (struct_with_array));
  if (s == 0) { abort(); }
  //@ close struct_with_array_pred(s);
  //@ close malloc_block_struct_with_array(s);

  
  //@ open struct_with_array_pred(s);
  s->ar[ 0] = 1;
  
  s->ar[ 1] = 5;
  
  s->ar[ 2] = 0;
  
  s->ar[ 6] = 2;
  s->ar[ 1] = s->ar[ 1] + s->ar[ 6];
  //@ close struct_with_array_pred(s);

  //@ open struct_with_array_pred(s);
  if (s->ar[i] == 7)
   { t += s->ar[2]; }
   else
   { assert false; }
  //@ close struct_with_array_pred(s);

  //@ open struct_with_array_pred(s);
  assert (s->ar[0] == 1);
  //@ close struct_with_array_pred(s);

  
  
  
  
  
  //@ open malloc_block_struct_with_array(s);
  //@ open struct_with_array_pred(s);
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

  //@ open points[..2] |-> _;
  //@ open bigArray[..10] |-> _;
  //@ open ar2[..55] |-> _;
  //@ open mystruct_pred(&my_global_nested_struct);
  return (t);
 }