#include "stdlib.h"
#include "assert.h"

struct tree
{
  int value;
  struct tree *left;
  struct tree *right;
};

/*@ predicate tree(struct tree *t) =
  t == 0 &*& emp
  ||
  t != 0 &*& t->value |-> _ &*& t->left |-> ?l &*& t->right |-> ?r &*& tree(l) &*& tree(r);
@*/

struct tree *init_tree(int x)
//@ requires true;
//@ ensures tree(result) &*& result != 0;
{
  struct tree *t = malloc(sizeof(struct tree));
  if (t != 0)
  {
    t->value = x;
    t->left = 0;
    t->right = 0;

    return t;
  }
  else
  {
    abort();
  }
}

void free_tree(struct tree *t)
//@ requires tree(t);
//@ ensures true;
{
  if (t == 0)
  {
  }
  else
  {

    struct tree *l = t->left;
    struct tree *r = t->right;
    free_tree(l);
    free_tree(r);
    free(t);
  }
}

bool contains(struct tree *t, int x)
//@ requires tree(t);
//@ ensures tree(t);
{
  if (t == 0)
  {

    return false;
  }
  else
  {

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
//@ requires tree(t) &*& t != 0;
//@ ensures tree(t);
{

  int v = t->value;
  struct tree *l = t->left;

  struct tree *r = t->right;

  if (x < v)
  {
    if (l != 0)
    {
      add(l, x);
    }
    else
    {
      struct tree *temp = init_tree(x);
      t->left = temp;
    }
  }
  else
  {
    if (v < x)
    {
      if (r != 0)
      {
        add(r, x);
      }
      else
      {
        struct tree *temp = init_tree(x);
        t->right = temp;
      }
    }
  }
}

int maximum(struct tree *t)
//@ requires tree(t) &*& t != 0;
//@ ensures tree(t);
{

  int v = t->value;
  struct tree *r = t->right;

  if (r == 0)
  {

    return v;
  }
  else
  {
    int m = maximum(r);

    return m;
  }
}

struct tree *remove(struct tree *t, int x)
//@ requires tree(t) &*& t != 0;
//@ ensures tree(result);
{

  int v = t->value;
  struct tree *l = t->left;

  struct tree *r = t->right;

  if (x < v)
  {
    if (l != 0)
    {
      struct tree *temp = remove(l, x);
      t->left = temp;

      return t;
    }
  }
  else if (v < x)
  {
    if (r != 0)
    {
      struct tree *temp = remove(r, x);
      t->right = temp;

      return t;
    }
  }
  else
  {
    if (l == 0)
    {
      if (r == 0)
      {

        free_tree(t);

        return 0;
      }
      else
      {

        free(t);
        return r;
      }
    }
    else
    {
      if (r == 0)
      {

        free(t);
        return l;
      }
      else
      {
        struct tree *temp = 0;
        int m = maximum(l);
        t->value = m;

        temp = remove(l, m);
        t->left = temp;

        return t;
      }
    }
  }
}

int main()
//@ requires true;
//@ ensures true;
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