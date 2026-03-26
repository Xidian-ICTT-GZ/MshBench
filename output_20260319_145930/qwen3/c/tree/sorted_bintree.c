/*@
#include "stdlib.h"
#include "assert.h"

struct tree{
  int value;
  struct tree *left;
  struct tree *right;
};

predicate tree(struct tree *t; int v, struct tree *l, struct tree *r) =
  t != 0 &*& t->value |-> v &*& t->left |-> l &*& t->right |-> r;

predicate tree_inorder(struct tree *t) =
  t == 0 ?
    true
  :
    tree(t, ?v, ?l, ?r) &*& tree_inorder(l) &*& tree_inorder(r) &*& 
    (l != 0 ? (maximum(l) <= v) : true) &*& 
    (r != 0 ? (v <= minimum(r)) : true);

fixpoint int maximum(struct tree *t) {
  switch (t) {
    case 0: return 0;
    case tree(v, l, r): return r == 0 ? v : maximum(r);
  }
}

fixpoint int minimum(struct tree *t) {
  switch (t) {
    case 0: return 0;
    case tree(v, l, r): return l == 0 ? v : minimum(l);
  }
}

fixpoint bool contains(struct tree *t, int x) {
  switch (t) {
    case 0: return false;
    case tree(v, l, r): return v == x ? true : (x < v ? contains(l, x) : contains(r, x));
  }
}

lemma void max_of_nonempty_is_value_or_in_right(struct tree *t)
  requires tree_inorder(t) &*& t != 0;
  ensures tree_inorder(t) &*& maximum(t) == (t->right == 0 ? t->value : maximum(t->right));
{
  open tree_inorder(t);
  if (t->right == 0) {
  } else {
    max_of_nonempty_is_value_or_in_right(t->right);
  }
}

lemma void min_of_nonempty_is_value_or_in_left(struct tree *t)
  requires tree_inorder(t) &*& t != 0;
  ensures tree_inorder(t) &*& minimum(t) == (t->left == 0 ? t->value : minimum(t->left));
{
  open tree_inorder(t);
  if (t->left == 0) {
  } else {
    min_of_nonempty_is_value_or_in_left(t->left);
  }
}

lemma void contains_preserved_by_adding_smaller(struct tree *t, int x, int y)
  requires tree_inorder(t) &*& contains(t, x) == true &*& y < minimum(t);
  ensures tree_inorder(t) &*& contains(t, x) == true;
{
  if (t == 0) {
  } else {
    open tree_inorder(t);
    if (t->left == 0) {
      assert(y < t->value);
    } else {
      min_of_nonempty_is_value_or_in_left(t->left);
      contains_preserved_by_adding_smaller(t->left, x, y);
    }
    contains_preserved_by_adding_smaller(t->right, x, y);
    close tree_inorder(t);
  }
}

lemma void contains_preserved_by_adding_larger(struct tree *t, int x, int y)
  requires tree_inorder(t) &*& contains(t, x) == true &*& maximum(t) < y;
  ensures tree_inorder(t) &*& contains(t, x) == true;
{
  if (t == 0) {
  } else {
    open tree_inorder(t);
    if (t->right == 0) {
      assert(t->value < y);
    } else {
      max_of_nonempty_is_value_or_in_right(t->right);
      contains_preserved_by_adding_larger(t->right, x, y);
    }
    contains_preserved_by_adding_larger(t->left, x, y);
    close tree_inorder(t);
  }
}
@*/

struct tree *init_tree(int x)
//@ requires true;
//@ ensures tree_inorder(result) &*& contains(result, x) == true;
{
  struct tree *t = malloc(sizeof(struct tree));
  if(t!=0){
    t->value=x;
    t->left=0;
    t->right=0;
    //@ close tree(t, x, 0, 0);
    //@ close tree_inorder(t);
    return t;
  }else{
	abort();
  }
}

void free_tree(struct tree *t)
//@ requires tree_inorder(t);
//@ ensures true;
{
  if(t==0){
    
  }else{
    //@ open tree_inorder(t);
    struct tree *l=t->left;
    struct tree *r=t->right;
    free_tree(l);
    free_tree(r);
    free(t);
  }
}

bool contains(struct tree *t,int x)
//@ requires tree_inorder(t);
//@ ensures tree_inorder(t) &*& result == contains(t, x);
{
  if(t==0){
    return false;
  }else{
    //@ open tree_inorder(t);
    int v=t->value;
    struct tree *l=t->left;
    struct tree *r=t->right;
    if(v==x){
      //@ close tree_inorder(t);
      return true;
    }else if(x < v){
      bool temp1=contains(l,x);
      //@ close tree_inorder(t);
      return temp1;
    }else{
      bool temp2=contains(r,x);
      //@ close tree_inorder(t);
      return temp2;
    }
  }
}

void add(struct tree *t, int x)
//@ requires tree_inorder(t) &*& contains(t, x) == false;
//@ ensures tree_inorder(t) &*& contains(t, x) == true;
{
  //@ open tree_inorder(t);
  int v=t->value;
  struct tree *l=t->left;
  struct tree *r=t->right;
  if(x < v){
    if(l!=0){
      add(l,x);
      //@ close tree_inorder(t);
    }else{
      struct tree *temp=init_tree(x);
      t->left=temp;
      //@ close tree_inorder(t);
    }
  }else{
    if(v < x){
      if(r!=0){
        add(r,x);
        //@ close tree_inorder(t);
      }else{
        struct tree *temp=init_tree(x);
        t->right=temp;
        //@ close tree_inorder(t);
      }
    }
  }
}

int maximum(struct tree *t)
//@ requires tree_inorder(t) &*& t != 0;
//@ ensures tree_inorder(t) &*& result == maximum(t);
{
  //@ open tree_inorder(t);
  int v=t->value;
  struct tree *r=t->right;
  if(r==0){
    //@ close tree_inorder(t);
    return v;
  }else{
    int m= maximum(r);
    //@ close tree_inorder(t);
    return m;
  }
}

struct tree* remove(struct tree *t, int x)
//@ requires tree_inorder(t) &*& contains(t, x) == true;
//@ ensures tree_inorder(result) &*& contains(result, x) == false;
{
  //@ open tree_inorder(t);
  int v=t->value;
  struct tree *l=t->left;
  struct tree *r=t->right;
  if(x < v){
    if(l!=0){
      struct tree *temp=remove(l,x);
      t->left=temp;
      //@ close tree_inorder(t);
      return t;
    }
  } else if(v < x){
    if(r!=0){
      struct tree *temp=remove(r,x);
      t->right=temp;
      //@ close tree_inorder(t);
      return t;
    }
  } else {
    if (l == 0) {
      if (r == 0) {
        free(t);
        return 0;
      } else {
        free(t);
        //@ close tree_inorder(r);
        return r;
      }
    } else {
      if(r==0){
        free(t);
        //@ close tree_inorder(l);
        return l;
      } else {
        struct tree *temp=0;
        int m=maximum(l);
        t->value=m;
        //@ assert tree_inorder(l);
        temp=remove(l,m);
        t->left=temp;
        //@ close tree_inorder(t);
        return t;
      }
    }
  }
  abort(); 
}

int main() 
//@ requires true;
//@ ensures true;
{
  struct tree *t1=0;
  struct tree *t2=0;
  struct tree *t3=0;
  bool a=false;
  bool b=false;
  bool c=false;
  bool d=false;
  bool e=false;
  bool f=false;

  t1 = init_tree(3);
  //@ close tree_inorder(t1);

  b= contains(t1,2);
  assert(!b);
  add(t1,2);

  a= contains(t1,2);
  assert(a);
  
  c= contains(t1,3);
  assert(c);

  t2=remove(t1,3);
  d= contains(t2,3);
  assert(!d);
  
  add(t2,3);
  e= contains(t2,2);
  assert(e);
  
  t3=remove(t2,3);
  f= contains(t3,3);
  assert(!f);

  free_tree(t3);

  return 0;
}