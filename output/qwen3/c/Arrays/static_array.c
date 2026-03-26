#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

#include <stdbool.h>

void check(bool b)

{
  assert(b);
}

typedef struct
{
  int x;
  int ar[7];
  int y;
} struct_with_array;

/*@ predicate struct_with_array_inv(struct_with_array* p) =
    p->x |-> ?x &*& p->ar[0] |-> ?a0 &*& p->ar[1] |-> ?a1 &*& p->ar[2] |-> ?a2 &*&
    p->ar[3] |-> ?a3 &*& p->ar[4] |-> ?a4 &*& p->ar[5] |-> ?a5 &*& p->ar[6] |-> ?a6 &*&
    p->y |-> ?y;
@*/

void check_local_inits(int x, int y)

{
  struct_with_array foo = {123, {2, x, 5, 7, 11, 13, y}, 456};
  struct_with_array bar = foo;
  char buf[3] = {1, 2, 3};

  //@ assert struct_with_array_inv(&foo);
  //@ assert struct_with_array_inv(&bar);
  //@ assert buf[0] |-> ?b0 &*& buf[1] |-> ?b1 &*& buf[2] |-> ?b2;
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

/*@ predicate mystruct_inv(struct mystruct* p) =
    p->s1.x |-> ?x &*& p->s1.ar[0] |-> ?a0 &*& p->s1.ar[1] |-> ?a1 &*& p->s1.ar[2] |-> ?a2 &*&
    p->s1.ar[3] |-> ?a3 &*& p->s1.ar[4] |-> ?a4 &*& p->s1.ar[5] |-> ?a5 &*& p->s1.ar[6] |-> ?a6 &*&
    p->s1.y |-> ?y &*& p->s2 |-> ?s2;
@*/

static void foo()

{
  struct mystruct my_local_nested_struct;

  memset(&my_local_nested_struct, 0, sizeof(struct mystruct));

  //@ assert mystruct_inv(&my_local_nested_struct);
  memset(&(&my_local_nested_struct)->s1, 0, sizeof(struct_with_array));

  //@ assert mystruct_inv(&my_local_nested_struct);
  assert(&my_global_nested_struct != &my_local_nested_struct);
  struct mystruct *sh = malloc(sizeof(struct mystruct));
  if (sh == 0)
    abort();
  //@ assert sh != 0 &*& malloc_block_mystruct(sh);
  assert(sh != &my_global_nested_struct);
  assert(sh != &my_local_nested_struct);
  (&(&my_global_nested_struct)->s1)->ar[5] = 100;
  (&(&my_local_nested_struct)->s1)->ar[5] = 200;

  //@ assert mystruct_inv(&my_local_nested_struct);
  (&sh->s1)->ar[5] = 300;

  //@ assert mystruct_inv(sh);
  free(sh);
}

static int ar2[55];

/*@ predicate ar2_inv() =
    ar2[0] |-> ?a0 &*& ar2[1] |-> ?a1 &*& ar2[2] |-> ?a2 &*& ar2[3] |-> ?a3 &*&
    ar2[4] |-> ?a4 &*& ar2[5] |-> ?a5 &*& ar2[6] |-> ?a6 &*& ar2[7] |-> ?a7 &*&
    ar2[8] |-> ?a8 &*& ar2[9] |-> ?a9 &*& ar2[10] |-> ?a10 &*& ar2[11] |-> ?a11 &*&
    ar2[12] |-> ?a12 &*& ar2[13] |-> ?a13 &*& ar2[14] |-> ?a14 &*& ar2[15] |-> ?a15 &*&
    ar2[16] |-> ?a16 &*& ar2[17] |-> ?a17 &*& ar2[18] |-> ?a18 &*& ar2[19] |-> ?a19 &*&
    ar2[20] |-> ?a20 &*& ar2[21] |-> ?a21 &*& ar2[22] |-> ?a22 &*& ar2[23] |-> ?a23 &*&
    ar2[24] |-> ?a24 &*& ar2[25] |-> ?a25 &*& ar2[26] |-> ?a26 &*& ar2[27] |-> ?a27 &*&
    ar2[28] |-> ?a28 &*& ar2[29] |-> ?a29 &*& ar2[30] |-> ?a30 &*& ar2[31] |-> ?a31 &*&
    ar2[32] |-> ?a32 &*& ar2[33] |-> ?a33 &*& ar2[34] |-> ?a34 &*& ar2[35] |-> ?a35 &*&
    ar2[36] |-> ?a36 &*& ar2[37] |-> ?a37 &*& ar2[38] |-> ?a38 &*& ar2[39] |-> ?a39 &*&
    ar2[40] |-> ?a40 &*& ar2[41] |-> ?a41 &*& ar2[42] |-> ?a42 &*& ar2[43] |-> ?a43 &*&
    ar2[44] |-> ?a44 &*& ar2[45] |-> ?a45 &*& ar2[46] |-> ?a46 &*& ar2[47] |-> ?a47 &*&
    ar2[48] |-> ?a48 &*& ar2[49] |-> ?a49 &*& ar2[50] |-> ?a50 &*& ar2[51] |-> ?a51 &*&
    ar2[52] |-> ?a52 &*& ar2[53] |-> ?a53 &*& ar2[54] |-> ?a54;
@*/

void mod_ar2(void)

{
  //@ requires ar2_inv();
  //@ ensures ar2_inv();
  ar2[1] = ar2[1] + ar2[26];
  return;
}

static struct_with_array bigArray[10] = {{100, {1, 2, 3, 4}, 200}, {300, {5, 6, 7}, 400}};

/*@ predicate bigArray_inv() =
    bigArray[0].x |-> ?x0 &*& bigArray[0].ar[0] |-> ?a00 &*& bigArray[0].ar[1] |-> ?a01 &*&
    bigArray[0].ar[2] |-> ?a02 &*& bigArray[0].ar[3] |-> ?a03 &*& bigArray[0].ar[4] |-> ?a04 &*&
    bigArray[0].ar[5] |-> ?a05 &*& bigArray[0].ar[6] |-> ?a06 &*& bigArray[0].y |-> ?y0 &*&
    bigArray[1].x |-> ?x1 &*& bigArray[1].ar[0] |-> ?a10 &*& bigArray[1].ar[1] |-> ?a11 &*&
    bigArray[1].ar[2] |-> ?a12 &*& bigArray[1].ar[3] |-> ?a13 &*& bigArray[1].ar[4] |-> ?a14 &*&
    bigArray[1].ar[5] |-> ?a15 &*& bigArray[1].ar[6] |-> ?a16 &*& bigArray[1].y |-> ?y1;
@*/

struct point
{
  int x;
  int y;
};

struct point points[] = {{10, 20}, {30, 40}};

/*@ predicate points_inv() =
    points[0].x |-> ?x0 &*& points[0].y |-> ?y0 &*& points[1].x |-> ?x1 &*& points[1].y |-> ?y1;
@*/

int main(int argc, char **argv)

{
  //@ assert mystruct_inv(&my_global_nested_struct);
  check((&(&my_global_nested_struct)->s1)->x == 42);
  check((&(&my_global_nested_struct)->s1)->ar[0] == 420);
  check((&(&my_global_nested_struct)->s1)->ar[6] == 426);
  check((&(&my_global_nested_struct)->s1)->y == -3);
  check((&my_global_nested_struct)->s2 == -99);

  struct_with_array *bigArrayPtr = bigArray;
  //@ assert bigArray_inv();
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

  //@ assert ar1[0] |-> 1 &*& ar1[1] |-> 7 &*& ar1[2] |-> 0 &*& ar1[26] |-> 2;
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
  //@ assert s != 0 &*& malloc_block_struct_with_array(s);
  s->ar[0] = 1;
  s->ar[1] = 5;
  s->ar[2] = 0;
  s->ar[6] = 2;
  s->ar[1] = s->ar[1] + s->ar[6];

  //@ assert s->ar[0] |-> 1 &*& s->ar[1] |-> 7 &*& s->ar[2] |-> 0 &*& s->ar[6] |-> 2;
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

  //@ assert ar2_inv();
  check(ar2[0] == 0);
  ar2[0] = 1;
  ar2[1] = 5;
  ar2[2] = 0;
  ar2[26] = 2;
  mod_ar2();

  //@ assert ar2[0] |-> 1 &*& ar2[1] |-> 7 &*& ar2[2] |-> 0 &*& ar2[26] |-> 2;
  if (ar2[i] == 7)
  {
    t += ar2[2];
  }
  else
  {
    assert false;
  }

  assert(ar2[1] == 7);

  //@ assert points_inv();
  assert(points[1].y == 40);

  int xs[] = {1, 2, 3}, ys[] = {4, 5, 6, 7};
  //@ assert xs[0] |-> 1 &*& xs[1] |-> 2 &*& xs[2] |-> 3;
  //@ assert ys[0] |-> 4 &*& ys[1] |-> 5 &*& ys[2] |-> 6 &*& ys[3] |-> 7;
  xs[1] = xs[2];
  //@ assert xs[0] |-> 1 &*& xs[1] |-> 3 &*& xs[2] |-> 3;
  assert(xs[1] == 3);
  ys[2] = ys[3];
  //@ assert ys[0] |-> 4 &*& ys[1] |-> 5 &*& ys[2] |-> 7 &*& ys[3] |-> 7;
  assert(ys[2] == 7);

  return (t);
}