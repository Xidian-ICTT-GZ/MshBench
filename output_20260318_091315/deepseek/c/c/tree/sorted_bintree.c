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

/*@
predicate bst(struct tree *t;) =
  t == 0 ? true : tree(t, ?v, ?l, ?r) &*& bst(l) &*& bst(r) &*&
  (l != 0 ? maximum(l) < v : true) &*&
  (r != 0 ? v < minimum(r) : true);
@*/

/*@
fixpoint int maximum(struct tree *t) {
  switch(t) {
    case 0: return 0;
    case tree(v, l, r): return r == 0 ? v : maximum(r);
  }
}
@*/

/*@
fixpoint int minimum(struct tree *t) {
  switch(t) {
    case 0: return 0;
    case tree(v, l, r): return l == 0 ? v : minimum(l);
  }
}
@*/

/*@
lemma void maximum_lemma(struct tree *t)
  requires bst(t) &*& t != 0;
  ensures bst(t) &*& t->value |-> ?v &*& t->right |-> ?r &*&
          (r != 0 ? maximum(r) == maximum(t) : v == maximum(t));
{
  open bst(t);
  if (t->right == 0) {
  } else {
    maximum_lemma(t->right);
  }
  close bst(t);
}
@*/

/*@
lemma void minimum_lemma(struct tree *t)
  requires bst(t) &*& t != 0;
  ensures bst(t) &*& t->value |-> ?v &*& t->left |-> ?l &*&
          (l != 0 ? minimum(l) == minimum(t) : v == minimum(t));
{
  open bst(t);
  if (t->left == 0) {
  } else {
    minimum_lemma(t->left);
  }
  close bst(t);
}
@*/

/*@
lemma void bst_left(struct tree *t)
  requires bst(t) &*& t != 0;
  ensures bst(t) &*& tree(t, ?v, ?l, ?r) &*& bst(l);
{
  open bst(t);
  close bst(t);
}
@*/

/*@
lemma void bst_right(struct tree *t)
  requires bst(t) &*& t != 0;
  ensures bst(t) &*& tree(t, ?v, ?l, ?r) &*& bst(r);
{
  open bst(t);
  close bst(t);
}
@*/

/*@
lemma void bst_join(struct tree *t)
  requires tree(t, ?v, ?l, ?r) &*& bst(l) &*& bst(r) &*&
           (l != 0 ? maximum(l) < v : true) &*&
           (r != 0 ? v < minimum(r) : true);
  ensures bst(t);
{
  close bst(t);
}
@*/

struct tree *init_tree(int x)
  //@ requires true;
  //@ ensures bst(result) &*& result != 0 &*& result->value |-> x;
{
  struct tree *t = malloc(sizeof(struct tree));
  if(t!=0){
    t->value=x;
    t->left=0;
    t->right=0;
    //@ close tree(t, x, 0, 0);
    //@ close bst(t);
    return t;
  }else{
	abort();
  }
}

void free_tree(struct tree *t)
  //@ requires bst(t);
  //@ ensures true;
{
  if(t==0){
    //@ open bst(t);
  }else{
    //@ open bst(t);
    struct tree *l=t->left;
    struct tree *r=t->right;
    //@ open tree(t, _, _, _);
    free_tree(l);
    free_tree(r);
    free(t);
  }
}

bool contains(struct tree *t,int x)
  //@ requires bst(t);
  //@ ensures bst(t) &*& result == true || result == false;
{
  if(t==0){
    //@ open bst(t);
    //@ close bst(t);
    return false;
  }else{
    //@ open bst(t);
    int v=t->value;
    struct tree *l=t->left;
    struct tree *r=t->right;
    //@ open tree(t, v, l, r);
    if(v==x){
      //@ close tree(t, v, l, r);
      //@ close bst(t);
      return true;
    }else if(x < v){
      bool temp1=contains(l,x);
      //@ close tree(t, v, l, r);
      //@ close bst(t);
      return temp1;
    }else{
      bool temp2=contains(r,x);
      //@ close tree(t, v, l, r);
      //@ close bst(t);
      return temp2;
    }
  }
}

void add(struct tree *t, int x)
  //@ requires bst(t) &*& t != 0;
  //@ ensures bst(t);
 {
  //@ open bst(t);
  int v=t->value;
  struct tree *l=t->left;
  //@ open tree(t, v, l, ?r);
  struct tree *r=t->right;
  //@ close tree(t, v, l, r);
  //@ close bst(t);
  if(x < v){
    if(l!=0){
      add(l,x);
      //@ bst_left(t);
      //@ maximum_lemma(l);
      //@ close bst(t);
    }else{
      struct tree *temp=init_tree(x);
      t->left=temp;
      //@ bst_left(t);
      //@ close bst(t);
    }
  }else{
    if(v < x){
      if(r!=0){
        add(r,x);
        //@ bst_right(t);
        //@ minimum_lemma(r);
        //@ close bst(t);
      }else{
        struct tree *temp=init_tree(x);
        t->right=temp;
        //@ bst_right(t);
        //@ close bst(t);
      }
    }
    //@ close bst(t);
  }
}

int maximum(struct tree *t)
  //@ requires bst(t) &*& t != 0;
  //@ ensures bst(t);
{
  //@ open bst(t);
  int v=t->value;
  struct tree *r=t->right;
  //@ open tree(t, v, ?l, r);
  //@ close tree(t, v, l, r);
  //@ close bst(t);
  if(r==0){
    return v;
  }else{
    int m= maximum(r);
    //@ bst_right(t);
    //@ maximum_lemma(r);
    //@ close bst(t);
    return m;
  }
}

struct tree* remove(struct tree *t, int x)
  //@ requires bst(t);
  //@ ensures bst(result);
{
  if (t == 0) {
    //@ open bst(t);
    //@ close bst(t);
    return 0;
  }
  //@ open bst(t);
  int v=t->value;
  struct tree *l=t->left;
  struct tree *r=t->right;
  //@ open tree(t, v, l, r);
  //@ close tree(t, v, l, r);
  //@ close bst(t);
  if(x < v){
    if(l!=0){
      struct tree *temp=remove(l,x);
      t->left=temp;
      //@ bst_left(t);
      //@ if (temp != 0) { maximum_lemma(temp); }
      //@ close bst(t);
      return t;
    }
    //@ close bst(t);
    return t;
  } else if(v < x){
    if(r!=0){
      struct tree *temp=remove(r,x);
      t->right=temp;
      //@ bst_right(t);
      //@ if (temp != 0) { minimum_lemma(temp); }
      //@ close bst(t);
      return t;
    }
    //@ close bst(t);
    return t;
  } else {
    if (l == 0) {
      if (r == 0) {
        //@ open bst(t);
        //@ open tree(t, v, l, r);
        free(t);
        //@ close bst(0);
        return 0;
      } else {
        //@ open bst(t);
        //@ open tree(t, v, l, r);
        free(t);
        //@ assert bst(r);
        return r;
      }
    } else {
      if(r==0){
        //@ open bst(t);
        //@ open tree(t, v, l, r);
        free(t);
        //@ assert bst(l);
        return l;
      } else {
        struct tree *temp=0;
        int m=maximum(l);
        t->value=m;
        //@ bst_left(t);
        temp=remove(l,m);
        t->left=temp;
        //@ bst_left(t);
        //@ if (temp != 0) { maximum_lemma(temp); }
        //@ close bst(t);
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