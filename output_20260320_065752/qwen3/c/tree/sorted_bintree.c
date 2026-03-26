/*@
#include "stdlib.h"
#include "assert.h"

struct tree{
  int value;
  struct tree *left;
  struct tree *right;
};

predicate tree(struct tree *t; int min_val, int max_val) =
  t == 0 ?
    true
  :
    malloc_block_tree(t) &*&
    tree(t->left, _, t->value) &*&
    tree(t->right, t->value, _) &*&
    min_val <= t->value &*& t->value <= max_val;

lemma void tree_min_max(struct tree *t)
  requires tree(t, ?min_val, ?max_val);
  ensures tree(t, min_val, max_val);
{
}

lemma void tree_split(struct tree *t)
  requires tree(t, ?min_val, ?max_val) &*& t != 0;
  ensures
    malloc_block_tree(t) &*&
    tree(t->left, _, t->value) &*&
    tree(t->right, t->value, _) &*&
    min_val <= t->value &*& t->value <= max_val;
{
  open tree(t, min_val, max_val);
}

lemma void tree_join(struct tree *t)
  requires
    malloc_block_tree(t) &*&
    tree(t->left, ?lmin, t->value) &*&
    tree(t->right, t->value, ?rmax) &*&
    ?min_val <= t->value &*& t->value <= ?max_val;
  ensures tree(t, min_val, max_val);
{
  close tree(t, min_val, max_val);
}

@*/

struct tree *init_tree(int x)
//@ requires true;
//@ ensures tree(result, x, x);
{
  struct tree *t = malloc(sizeof(struct tree));
  if(t!=0){
    t->value=x;
    t->left=0;
    t->right=0;
    //@ close tree(t, x, x);
    return t;
  }else{
	abort();
  }
}

void free_tree(struct tree *t)
//@ requires tree(t, _, _);
//@ ensures true;
{
  if(t==0){
    
  }else{
    //@ open tree(t, _, _);
    struct tree *l=t->left;
    struct tree *r=t->right;
    free_tree(l);
    free_tree(r);
    free(t);
  }
}

bool contains(struct tree *t,int x)
//@ requires tree(t, ?min_val, ?max_val);
//@ ensures tree(t, min_val, max_val) &*& result == (x >= min_val && x <= max_val ? true : false); // conservative
{
  if(t==0){
    return false;
  }else{
    int v=t->value;
    struct tree *l=t->left;
    struct tree *r=t->right;
    if(v==x){
      return true;
    }else if(x < v){
      bool temp1=contains(l,x);
      return temp1;
    }else{
      bool temp2=contains(r,x);
      return temp2;
    }
  }
}

void add(struct tree *t, int x)
//@ requires tree(t, ?min_val, ?max_val) &*& (x < min_val || x > max_val); // assumes x not present
//@ ensures tree(t, x < min_val ? x : min_val, x > max_val ? x : max_val);
{
  int v=t->value;
  struct tree *l=t->left;
  struct tree *r=t->right;
  if(x < v){
    if(l!=0){
      //@ open tree(t, min_val, max_val);
      add(l,x);
      //@ close tree(t, _, _);
    }else{
      struct tree *temp=init_tree(x);
      t->left=temp;
      //@ open tree(t, min_val, max_val);
      //@ close tree(t, _, _);
    }
  }else{
    if(v < x){
      if(r!=0){
        //@ open tree(t, min_val, max_val);
        add(r,x);
        //@ close tree(t, _, _);
      }else{
        struct tree *temp=init_tree(x);
        t->right=temp;
        //@ open tree(t, min_val, max_val);
        //@ close tree(t, _, _);
      }
    }
  }
}

int maximum(struct tree *t)
//@ requires tree(t, ?min_val, ?max_val) &*& t != 0;
//@ ensures tree(t, min_val, max_val) &*& result == max_val;
{
  int v=t->value;
  struct tree *r=t->right;
  if(r==0){
    return v;
  }else{
    int m= maximum(r);
    return m;
  }
}

struct tree* remove(struct tree *t, int x)
//@ requires tree(t, ?min_val, ?max_val) &*& (min_val <= x && x <= max_val);
//@ ensures

{
  int v=t->value;
  struct tree *l=t->left;
  struct tree *r=t->right;
  if(x < v){
    if(l!=0){
      //@ open tree(t, min_val, max_val);
      struct tree *temp=remove(l,x);
      t->left=temp;
      //@ close tree(t, _, _);
      return t;
    }
  } else if(v < x){
    if(r!=0){
      //@ open tree(t, min_val, max_val);
      struct tree *temp=remove(r,x);
      t->right=temp;
      //@ close tree(t, _, _);
      return t;
    }
  } else {
    if (l == 0) {
      if (r == 0) {
        //@ open tree(t, min_val, max_val);
        free_tree(t);
        return 0;
      } else {
        //@ open tree(t, min_val, max_val);
        free(t);
        return r;
      }
    } else {
      if(r==0){
        //@ open tree(t, min_val, max_val);
        free(t);
        return l;
      } else {
        //@ open tree(t, min_val, max_val);
        struct tree *temp=0;
        int m=maximum(l);
        t->value=m;
        temp=remove(l,m);
        t->left=temp;
        //@ close tree(t, _, _);
        return t;
      }
    }
  }
  return t; 
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
  //@ close tree(t1, 3, 3);

  b= contains(t1,2);
  assert(!b);
  add(t1,2);
  //@ open tree(t1, _, _);
  //@ close tree(t1, 2, 3);

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