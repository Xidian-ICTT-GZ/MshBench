#include "stdlib.h"
#include "assert.h"

struct tree
{
  int value;
  struct tree *left;
  struct tree *right;
};

/*@ predicate tree(struct tree *t; int x) =
    t == 0 ? true :
    t->value |-> x &*&
    tree(t->left, ?l) &*&
    tree(t->right, ?r);
@*/

/*@ predicate bst(struct tree *t; int min, int max) =
    t == 0 ? true :
    t->value |-> ?v &*&
    min < v &*& v < max &*&
    bst(t->left, min, v) &*&
    bst(t->right, v, max);
@*/

/*@ lemma void bst_implies_tree(struct tree *t; int min, int max)
    requires bst(t, min, max);
    ensures tree(t, ?x);
{
    if (t != 0) {
        open bst(t, min, max);
        close tree(t, t->value);
    }
}
@*/

/*@ lemma void tree_implies_bst(struct tree *t; int x)
    requires tree(t, x);
    ensures bst(t, INT_MIN, INT_MAX);
{
    if (t != 0) {
        open tree(t, x);
        close bst(t, INT_MIN, INT_MAX);
    }
}
@*/

struct tree *init_tree(int x)

{
  struct tree *t = malloc(sizeof(struct tree));
  //@ requires true;
  //@ ensures tree(result, x);
  if (t != 0)
  {
    t->value = x;
    t->left = 0;
    t->right = 0;

    //@ close tree(t, x);
    return t;
  }
  else
  {
    abort();
  }
}

void free_tree(struct tree *t)

{
  //@ requires tree(t, ?x);
  //@ ensures true;
  if (t == 0)
  {
  }
  else
  {
    //@ open tree(t, ?x);
    struct tree *l = t->left;
    struct tree *r = t->right;
    free_tree(l);
    free_tree(r);
    free(t);
  }
}

bool contains(struct tree *t, int x)

{
  //@ requires tree(t, ?v);
  //@ ensures result == (t != 0 && (t->value == x || contains(t->left, x) || contains(t->right, x)));
  if (t == 0)
  {
    return false;
  }
  else
  {
    //@ open tree(t, ?v);
    int v = t->value;
    struct tree *l = t->left;
    struct tree *r = t->right;
    if (v == x)
    {
      return true;
    }
    else if (x < v)
    {
      bool temp1 = contains(l, x);
      return temp1;
    }
    else
    {
      bool temp2 = contains(r, x);
      return temp2;
    }
  }
}

void add(struct tree *t, int x)

{
  //@ requires tree(t, ?v) &*& x != v;
  //@ ensures tree(t, ?w);
  int v = t->value;
  struct tree *l = t->left;
  struct tree *r = t->right;

  if (x < v)
  {
    if (l != 0)
    {
      //@ open tree(t, v);
      //@ close tree(t, v);
      add(l, x);
    }
    else
    {
      //@ open tree(t, v);
      struct tree *temp = init_tree(x);
      t->left = temp;
      //@ close tree(t, v);
    }
  }
  else
  {
    if (v < x)
    {
      if (r != 0)
      {
        //@ open tree(t, v);
        //@ close tree(t, v);
        add(r, x);
      }
      else
      {
        //@ open tree(t, v);
        struct tree *temp = init_tree(x);
        t->right = temp;
        //@ close tree(t, v);
      }
    }
  }
}

int maximum(struct tree *t)

{
  //@ requires tree(t, ?v) &*& t != 0;
  //@ ensures result == ?m &*& tree(t, m);
  int v = t->value;
  struct tree *r = t->right;

  if (r == 0)
  {
    return v;
  }
  else
  {
    //@ open tree(t, v);
    int m = maximum(r);
    //@ close tree(t, m);
    return m;
  }
}

struct tree *remove(struct tree *t, int x)

{
  //@ requires tree(t, ?v);
  //@ ensures tree(result, ?w);
  int v = t->value;
  struct tree *l = t->left;
  struct tree *r = t->right;

  if (x < v)
  {
    if (l != 0)
    {
      //@ open tree(t, v);
      struct tree *temp = remove(l, x);
      t->left = temp;
      //@ close tree(t, v);
      return t;
    }
  }
  else if (v < x)
  {
    if (r != 0)
    {
      //@ open tree(t, v);
      struct tree *temp = remove(r, x);
      t->right = temp;
      //@ close tree(t, v);
      return t;
    }
  }
  else
  {
    if (l == 0)
    {
      if (r == 0)
      {
        //@ open tree(t, v);
        free_tree(t);
        return 0;
      }
      else
      {
        //@ open tree(t, v);
        free(t);
        return r;
      }
    }
    else
    {
      if (r == 0)
      {
        //@ open tree(t, v);
        free(t);
        return l;
      }
      else
      {
        //@ open tree(t, v);
        struct tree *temp = 0;
        int m = maximum(l);
        t->value = m;
        temp = remove(l, m);
        t->left = temp;
        //@ close tree(t, m);
        return t;
      }
    }
  }
}

int main()

{
  struct tree *t1 = 0;
  struct tree *t2 = 0;
  struct tree *t3 = 0;
  bool a = false;
  bool b = false;
  bool c = false;
  bool d = false;
  bool e = false;
  bool f = false;

  t1 = init_tree(3);

  b = contains(t1, 2);
  assert(!b);
  add(t1, 2);

  a = contains(t1, 2);
  assert(a);

  c = contains(t1, 3);
  assert(c);

  t2 = remove(t1, 3);
  d = contains(t2, 3);
  assert(!d);

  add(t2, 3);
  e = contains(t2, 2);
  assert(e);

  t3 = remove(t2, 3);
  f = contains(t3, 3);
  assert(!f);

  free_tree(t3);

  return 0;
}