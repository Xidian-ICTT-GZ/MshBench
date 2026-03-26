#include "stdlib.h"
#include "assert.h"

/*@
predicate tree(struct tree *t; int min, int max) =
    t == 0 ?
        emp
    :
        t->value |-> ?v &*& t->left |-> ?l &*& t->right |-> ?r &*&
        v >= min &*& v <= max &*&
        tree(l, min, v) &*& tree(r, v, max);
@*/

struct tree{
  int value;
  struct tree *left;
  struct tree *right;
};

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
    //@ requires tree(t, _, _);
    //@ ensures tree(t, _, _) &*& result == (t != 0 && (x == t->value || (x < t->value ? contains(t->left,x) : contains(t->right,x))));
{
  if(t==0){
    //@ close tree(0, _, _);
    return false;
  }else{
    //@ open tree(t, _, _);
    int v=t->value;
    struct tree *l=t->left;
    struct tree *r=t->right;
    if(v==x){
      //@ close tree(t, _, _);
      return true;
    }else if(x < v){
      bool temp1=contains(l,x);
      //@ close tree(t, _, _);
      return temp1;
    }else{
      bool temp2=contains(r,x);
      //@ close tree(t, _, _);
      return temp2;
    }
  }
}

void add(struct tree *t, int x)
    //@ requires tree(t, ?min, ?max) &*& ! (min <= x && x <= max);
    //@ ensures tree(t, min < x ? min : x, max > x ? max : x);
{
  //@ open tree(t, min, max);
  int v=t->value;
  struct tree *l=t->left;
  struct tree *r=t->right;
  if(x < v){
    if(l!=0){
      add(l,x);
    }else{
      struct tree *temp=init_tree(x);
      t->left=temp;
    }
  }else{
    if(v < x){
      if(r!=0){
        add(r,x);
      }else{
        struct tree *temp=init_tree(x);
        t->right=temp;
      }
    }
  }
  //@ close tree(t, min, max);
}

int maximum(struct tree *t)
    //@ requires tree(t, _, _);
    //@ ensures tree(t, _, _) &*& result >= t->value;
{
  //@ open tree(t, _, _);
  int v=t->value;
  struct tree *r=t->right;
  if(r==0){
    //@ close tree(t, _, _);
    return v;
  }else{
    int m= maximum(r);
    //@ close tree(t, _, _);
    return m;
  }
}

struct tree* remove(struct tree *t, int x)
    //@ requires tree(t, _, _) &*& t != 0;
    //@ ensures tree(result, _, _);
{
  //@ open tree(t, _, _);
  int v=t->value;
  struct tree *l=t->left;
  struct tree *r=t->right;
  if(x < v){
    if(l!=0){
      struct tree *temp=remove(l,x);
      t->left=temp;
      //@ close tree(t, _, _);
      return t;
    }
  } else if(v < x){
    if(r!=0){
      struct tree *temp=remove(r,x);
      t->right=temp;
      //@ close tree(t, _, _);
      return t;
    }
  } else {
    if (l == 0) {
      if (r == 0) {
        free_tree(t);
        return 0;
      } else {
        free(t);
        //@ close tree(r, _, _);
        return r;
      }
    } else {
      if(r==0){
        free(t);
        //@ close tree(l, _, _);
        return l;
      } else {
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
  //@ close tree(t, _, _);
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