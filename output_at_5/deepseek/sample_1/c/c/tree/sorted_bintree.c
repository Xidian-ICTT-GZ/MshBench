#include "stdlib.h"
#include "assert.h"

struct tree{
  int value;
  struct tree *left;
  struct tree *right;
};

/*@
predicate tree(struct tree *t; int v, struct tree *l, struct tree *r) =
  t->value |-> v &*& t->left |-> l &*& t->right |-> r &*& malloc_block_tree(t);
@*/

struct tree *init_tree(int x)
  //@ requires true;
  //@ ensures tree(result, x, 0, 0);
{
  struct tree *t = malloc(sizeof(struct tree));
  if(t!=0){
    t->value=x;
    t->left=0;
    t->right=0;
    //@ close tree(t, x, 0, 0);
    return t;
  }else{
	abort();
  }
}

void free_tree(struct tree *t)
  //@ requires tree(t, _, _, _);
  //@ ensures true;
{
  if(t==0){
    //@ open tree(t, _, _, _);
  }else{
    //@ open tree(t, _, _, _);
    struct tree *l=t->left;
    struct tree *r=t->right;
    free_tree(l);
    free_tree(r);
    free(t);
  }
}

bool contains(struct tree *t,int x)
  //@ requires tree(t, ?v, ?l, ?r);
  //@ ensures tree(t, v, l, r) &*& result == true || result == false;
{
  if(t==0){
    //@ open tree(t, _, _, _);
    return false;
  }else{
    //@ open tree(t, v, l, r);
    int v=t->value;
    struct tree *l=t->left;
    struct tree *r=t->right;
    if(v==x){
      //@ close tree(t, v, l, r);
      return true;
    }else if(x < v){
      bool temp1=contains(l,x);
      //@ close tree(t, v, l, r);
      return temp1;
    }else{
      bool temp2=contains(r,x);
      //@ close tree(t, v, l, r);
      return temp2;
    }
  }
}

void add(struct tree *t, int x)
  //@ requires tree(t, ?v, ?l, ?r);
  //@ ensures tree(t, v, l, r);
 {
  //@ open tree(t, v, l, r);
  int v=t->value;
  struct tree *l=t->left;
  //@ assert tree(l, _, _, _);
  struct tree *r=t->right;
  //@ assert tree(r, _, _, _);
  if(x < v){
    if(l!=0){
      add(l,x);
      //@ close tree(t, v, l, r);
    }else{
      struct tree *temp=init_tree(x);
      t->left=temp;
      //@ close tree(t, v, temp, r);
    }
  }else{
    if(v < x){
      if(r!=0){
        add(r,x);
        //@ close tree(t, v, l, r);
      }else{
        struct tree *temp=init_tree(x);
        t->right=temp;
        //@ close tree(t, v, l, temp);
      }
    }else{
      //@ close tree(t, v, l, r);
    }
  }
}

int maximum(struct tree *t)
  //@ requires tree(t, ?v, ?l, ?r);
  //@ ensures tree(t, v, l, r);
{
  //@ open tree(t, v, l, r);
  int v=t->value;
  struct tree *r=t->right;
  //@ assert tree(r, _, _, _);
  if(r==0){
    //@ close tree(t, v, l, r);
    return v;
  }else{
    int m= maximum(r);
    //@ close tree(t, v, l, r);
    return m;
  }
}

struct tree* remove(struct tree *t, int x)
  //@ requires tree(t, ?v, ?l, ?r);
  //@ ensures tree(result, _, _, _);
{
  //@ open tree(t, v, l, r);
  int v=t->value;
  struct tree *l=t->left;
  //@ assert tree(l, _, _, _);
  struct tree *r=t->right;
  //@ assert tree(r, _, _, _);
  
  if(x < v){
    if(l!=0){
      struct tree *temp=remove(l,x);
      t->left=temp;
      //@ close tree(t, v, temp, r);
      return t;
    }else{
      //@ close tree(t, v, l, r);
      return t;
    }
  } else if(v < x){
    if(r!=0){
      struct tree *temp=remove(r,x);
      t->right=temp;
      //@ close tree(t, v, l, temp);
      return t;
    }else{
      //@ close tree(t, v, l, r);
      return t;
    }
  } else {
    if (l == 0) {
      if (r == 0) {
        //@ open tree(l, _, _, _);
        //@ open tree(r, _, _, _);
        free(t);
        return 0;
      } else {
        free(t);
        return r;
      }
    } else {
      if(r==0){
        free(t);
        return l;
      } else {
        struct tree *temp=0;
        int m=maximum(l);
        t->value=m;
        temp=remove(l,m);
        t->left=temp;
        //@ close tree(t, m, temp, r);
        return t;
      }
    }
  }
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