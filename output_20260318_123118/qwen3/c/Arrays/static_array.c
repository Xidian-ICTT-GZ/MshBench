/*@ predicate struct_with_array(struct_with_array *p; int x_val, int y_val, int ar0, int ar1, int ar2, int ar3, int ar4, int ar5, int ar6) =
    p->x |-> x_val &*& p->y |-> y_val &*&
    p->ar[0] |-> ar0 &*& p->ar[1] |-> ar1 &*& p->ar[2] |-> ar2 &*&
    p->ar[3] |-> ar3 &*& p->ar[4] |-> ar4 &*& p->ar[5] |-> ar5 &*& p->ar[6] |-> ar6;
@*/

/*@ predicate mystruct(struct mystruct *p; int s1_x, int s1_y, int s1_ar0, int s1_ar1, int s1_ar2, int s1_ar3, int s1_ar4, int s1_ar5, int s1_ar6, int s2_val) =
    struct_with_array(&p->s1, s1_x, s1_y, s1_ar0, s1_ar1, s1_ar2, s1_ar3, s1_ar4, s1_ar5, s1_ar6) &*& p->s2 |-> s2_val;
@*/

/*@ predicate array_int(int *a, int n, int v0, int v1, int v2, int v3, int v4, int v5, int v6, int v7, int v8, int v9,
                      int v10, int v11, int v12, int v13, int v14, int v15, int v16, int v17, int v18, int v19,
                      int v20, int v21, int v22, int v23, int v24, int v25, int v26, int v27, int v28, int v29,
                      int v30, int v31, int v32, int v33, int v34, int v35, int v36, int v37, int v38, int v39,
                      int v40, int v41, int v42, int v43, int v44, int v45, int v46, int v47, int v48, int v49,
                      int v50, int v51, int v52, int v53, int v54) =
    a[0] |-> v0 &*& a[1] |-> v1 &*& a[2] |-> v2 &*& a[3] |-> v3 &*& a[4] |-> v4 &*&
    a[5] |-> v5 &*& a[6] |-> v6 &*& a[7] |-> v7 &*& a[8] |-> v8 &*& a[9] |-> v9 &*&
    a[10] |-> v10 &*& a[11] |-> v11 &*& a[12] |-> v12 &*& a[13] |-> v13 &*& a[14] |-> v14 &*&
    a[15] |-> v15 &*& a[16] |-> v16 &*& a[17] |-> v17 &*& a[18] |-> v18 &*& a[19] |-> v19 &*&
    a[20] |-> v20 &*& a[21] |-> v21 &*& a[22] |-> v22 &*& a[23] |-> v23 &*& a[24] |-> v24 &*&
    a[25] |-> v25 &*& a[26] |-> v26 &*& a[27] |-> v27 &*& a[28] |-> v28 &*& a[29] |-> v29 &*&
    a[30] |-> v30 &*& a[31] |-> v31 &*& a[32] |-> v32 &*& a[33] |-> v33 &*& a[34] |-> v34 &*&
    a[35] |-> v35 &*& a[36] |-> v36 &*& a[37] |-> v37 &*& a[38] |-> v38 &*& a[39] |-> v39 &*&
    a[40] |-> v40 &*& a[41] |-> v41 &*& a[42] |-> v42 &*& a[43] |-> v43 &*& a[44] |-> v44 &*&
    a[45] |-> v45 &*& a[46] |-> v46 &*& a[47] |-> v47 &*& a[48] |-> v48 &*& a[49] |-> v49 &*&
    a[50] |-> v50 &*& a[51] |-> v51 &*& a[52] |-> v52 &*& a[53] |-> v53 &*& a[54] |-> v54;
@*/

void check (bool b)
//@ requires true;
//@ ensures true;
{
  assert(b);
}

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

void mod_ar2 (void)
//@ requires array_int(ar2, 55, ?v0, ?v1, ?v2, ?v3, ?v4, ?v5, ?v6, ?v7, ?v8, ?v9,

//@ ensures array_int(ar2, 55, v0, v1 + v26, v2, v3, v4, v5, v6, v7, v8, v9,

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