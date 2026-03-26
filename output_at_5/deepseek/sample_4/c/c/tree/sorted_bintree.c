#include "stdlib.h"
#include "assert.h"

struct tree{
  int value;
  struct tree *left;
  struct tree *right;
};

/*@
predicate tree(struct tree *t;) =
  t == 0 ?
    true
  :
    t->value |-> ?v &*& t->left |-> ?l &*& t->right |-> ?r &*& malloc_block_tree(t) &*& tree(l) &*& tree(r);
@*/

struct tree *init_tree(int x)
  //@ requires true;
  //@ ensures tree(result);
{
  struct tree *t = malloc(sizeof(struct tree));
  if(t!=0){
    t->value=x;
    t->left=0;
    t->right=0;
    //@ close tree(0);
    //@ close tree(t);
    return t;
  }else{
	abort();
  }
}

void free_tree(struct tree *t)
  //@ requires tree(t);
  //@ ensures true;
{
  if(t==0){
    //@ open tree(t);
  }else{
    //@ open tree(t);
    struct tree *l=t->left;
    struct tree *r=t->right;
    free_tree(l);
    free_tree(r);
    free(t);
  }
}

bool contains(struct tree *t,int x)
  //@ requires tree(t);
  //@ ensures tree(t);
{
  if(t==0){
    //@ open tree(t);
    //@ close tree(t);
    return false;
  }else{
    //@ open tree(t);
    int v=t->value;
    struct tree *l=t->left;
    struct tree *r=t->right;
    if(v==x){
      //@ close tree(t);
      return true;
    }else if(x < v){
      bool temp1=contains(l,x);
      //@ close tree(t);
      return temp1;
    }else{
      bool temp2=contains(r,x);
      //@ close tree(t);
      return temp2;
    }
  }
}

void add(struct tree *t, int x)
  //@ requires tree(t);
  //@ ensures tree(t);
 {
  if(t==0){
    //@ open tree(t);
    //@ close tree(t);
    return;
  }
  //@ open tree(t);
  int v=t->value;
  struct tree *l=t->left;
  struct tree *r=t->right;
  if(x < v){
    if(l!=0){
      add(l,x);
      //@ close tree(t);
    }else{
      struct tree *temp=init_tree(x);
      //@ assert tree(temp);
      t->left=temp;
      //@ close tree(t);
    }
  }else{
    if(v < x){
      if(r!=0){
        add(r,x);
        //@ close tree(t);
      }else{
        struct tree *temp=init_tree(x);
        //@ assert tree(temp);
        t->right=temp;
        //@ close tree(t);
      }
    }else{
      //@ close tree(t);
    }
  }
}

int maximum(struct tree *t)
  //@ requires tree(t) &*& t != 0;
  //@ ensures tree(t);
{
  //@ open tree(t);
  int v=t->value;
  struct tree *r=t->right;
  if(r==0){
    //@ close tree(t);
    return v;
  }else{
    int m= maximum(r);
    //@ close tree(t);
    return m;
  }
}

struct tree* remove(struct tree *t, int x)
  //@ requires tree(t);
  //@ ensures tree(result);
{
  if(t==0){
    //@ open tree(t);
    //@ close tree(t);
    return 0;
  }
  //@ open tree(t);
  int v=t->value;
  struct tree *l=t->left;
  struct tree *r=t->right;
  
  if(x < v){
    if(l!=0){
      struct tree *temp=remove(l,x);
      t->left=temp;
      //@ close tree(t);
      return t;
    }else{
      //@ close tree(t);
      return t;
    }
  } else if(v < x){
    if(r!=0){
      struct tree *temp=remove(r,x);
      t->right=temp;
      //@ close tree(t);
      return t;
    }else{
      //@ close tree(t);
      return t;
    }
  } else {
    if (l == 0) {
      if (r == 0) {
        free(t);
        //@ close tree(0);
        return 0;
      } else {
        //@ open tree(r);
        //@ close tree(r);
        free(t);
        return r;
      }
    } else {
      if(r==0){
        //@ open tree(l);
        //@ close tree(l);
        free(t);
        return l;
      } else {
        struct tree *temp=0;
        int m=maximum(l);
        t->value=m;
        temp=remove(l,m);
        t->left=temp;
        //@ close tree(t);
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
  //@ assert tree(t1);

  b= contains(t1,2);
  //@ assert tree(t1);
  assert(!b);
  add(t1,2);
  //@ assert tree(t1);

  a= contains(t1,2);
  //@ assert tree(t1);
  assert(a);
  
  c= contains(t1,3);
  //@ assert tree(t1);
  assert(c);

  t2=remove(t1,3);
  //@ assert tree(t2);
  d= contains(t2,3);
  //@ assert tree(t2);
  assert(!d);
  
  add(t2,3);
  //@ assert tree(t2);
  e= contains(t2,2);
  //@ assert tree(t2);
  assert(e);
  
  t3=remove(t2,3);
  //@ assert tree(t3);
  f= contains(t3,3);
  //@ assert tree(t3);
  assert(!f);

  free_tree(t3);

  return 0;
}