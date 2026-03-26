#include "stdlib.h"
#include "assert.h"

struct tree{
  int value;
  struct tree *left;
  struct tree *right;
};

/*@
inductive bintree = empty | tree(int, bintree, bintree);

predicate Tree(struct tree *t; bintree b) =
  t == 0 ?
    b == empty
  :
    t->value |-> ?v &*& t->left |-> ?l &*& t->right |-> ?r &*&
    malloc_block_tree(t) &*&
    Tree(l, ?bl) &*& Tree(r, ?br) &*&
    b == tree(v, bl, br);

fixpoint int max(bintree b) {
  switch(b) {
    case empty: return 0;
    case tree(v, l, r): return r == empty ? v : max(r);
  }
}

fixpoint int min(bintree b) {
  switch(b) {
    case empty: return 0;
    case tree(v, l, r): return l == empty ? v : min(l);
  }
}

fixpoint bool inorder(bintree b) {
  switch(b) {
    case empty: return true;
    case tree(v, l, r):
      return inorder(l) && inorder(r) &&
             (l == empty || max(l) < v) &&
             (r == empty || v < min(r));
  }
}

fixpoint bool t_contains(bintree b, int x) {
  switch(b) {
    case empty: return false;
    case tree(v, l, r): return v == x || t_contains(l, x) || t_contains(r, x);
  }
}

fixpoint bintree tree_add(bintree b, int x) {
  switch(b) {
    case empty: return tree(x, empty, empty);
    case tree(v, l, r):
      return x < v ? tree(v, tree_add(l, x), r) :
             (v < x ? tree(v, l, tree_add(r, x)) : b);
  }
}

fixpoint bintree tree_rem(bintree b, int x) {
  switch(b) {
    case empty: return empty;
    case tree(v, l, r):
      return x < v ? tree(v, tree_rem(l, x), r) :
             (v < x ? tree(v, l, tree_rem(r, x)) :
              (l == empty ? r :
               (r == empty ? l :
                tree(max(l), tree_rem(l, max(l)), r))));
  }
}

lemma void min_le_max(bintree r)
  requires r != empty &*& inorder(r) == true;
  ensures min(r) <= max(r);
{
  switch(r) {
    case empty:
    case tree(a, b, c):
      if (b != empty) {
        min_le_max(b);
      }
      if (c != empty) {
        min_le_max(c);
      }
  }
}

lemma void contains_max(bintree r)
  requires r != empty &*& inorder(r) == true;
  ensures t_contains(r, max(r)) == true;
{
  switch(r) {
    case empty:
    case tree(a, b, c):
      if (c != empty) {
        min_le_max(c);
        contains_max(c);
        if (a == max(r)) {} else {}
        if ((max(r) < a) == true) {} else {}
      }
  }
}

lemma void contains_min(bintree r)
  requires r != empty &*& inorder(r) == true;
  ensures t_contains(r, min(r)) == true;
{
  switch(r) {
    case empty:
    case tree(a, b, c):
      if (b != empty) {
        min_le_max(b);
        contains_min(b);
        if (a == min(r)) {} else {}
        if ((min(r) < a) == true) {} else {}
      }
  }
}

lemma void max_conj_add(bintree l, int v, int x)
  requires x < v &*& (max(l) < v || l == empty) &*& inorder(l) == true;
  ensures max(tree_add(l, x)) < v &*& inorder(l) == true;
{
  switch(l) {
    case empty:
    case tree(a, b, c):
      if (x < a) {
        if (b == empty) {} else {}
        max_conj_add(b, a, x);
      }
      if (a < x) {
        if (c == empty) {} else {}
        max_conj_add(c, v, x);
      }
      if ((x < a) == true) {} else { if (x == a) {} else {} }
      if (c == empty) {} else {}
      if (x == a) {} else {}
      if (tree_add(c, x) == empty) {} else {}
  }
}

lemma void min_conj_add(bintree r, int v, int x)
  requires v < x &*& (v < min(r) || r == empty) &*& inorder(r) == true;
  ensures v < min(tree_add(r, x)) &*& inorder(r) == true;
{
  switch(r) {
    case empty:
    case tree(a, b, c):
      if (a < x) {
        min_conj_add(c, a, x);
      }
      if (x < a) {
        min_conj_add(b, v, x);
      }
  }
}

lemma void max_conj_rem(bintree l, int v, int x)
  requires x < v &*& (max(l) < v || l == empty) &*& inorder(l) == true;
  ensures (max(tree_rem(l, x)) < v || tree_rem(l, x) == empty) &*& inorder(l) == true;
{
  switch(l) {
    case empty:
    case tree(a, b, c):
      if (x < a) {
        max_conj_rem(b, a, x);
      }
      if (a < x) {
        max_conj_rem(c, v, x);
      }
  }
}

lemma void tree_add_inorder(bintree b, int x)
  requires inorder(b) == true &*& t_contains(b, x) == false;
  ensures inorder(tree_add(b, x)) == true &*& t_contains(tree_add(b, x), x) == true;
{
  switch (b) {
    case empty:
    case tree(v, l, r):
      if (x < v) {
        max_conj_add(l, v, x);
        tree_add_inorder(l, x);
      }
      if (v < x) {
        min_conj_add(r, v, x);
        tree_add_inorder(r, x);
      }
  }
}

lemma void min_all(bintree r, int x)
  requires t_contains(r, x) == true &*& inorder(r) == true;
  ensures min(r) <= x;
{
  switch(r) {
    case empty:
    case tree(a, b, c):
      if (b != empty) {
        contains_max(b);
        min_all(b, max(b));
      }
      if (t_contains(b, x)) {
        min_all(b, x);
      }
  }
}

lemma void max_all(bintree r, int x)
  requires inorder(r) == true &*& t_contains(r, x) == true &*& x != max(r);
  ensures x < max(r);
{
  switch(r) {
    case empty:
    case tree(a, b, c):
      if (c != empty) {
        contains_min(c);
        min_le_max(c);
      }
      if (t_contains(c, x)) {
        max_all(c, x);
      }
  }
}

lemma void min_conj_rem(bintree r, int v, int x)
  requires v < x &*& (v < min(r) || r == empty) &*& inorder(r) == true;
  ensures (v < min(tree_rem(r, x)) || tree_rem(r, x) == empty) &*& inorder(r) == true;
{
  switch(r) {
    case empty:
    case tree(a, b, c):
      if (a < x) {
        min_conj_rem(c, a, x);
      }
      if (x < a) {
        min_conj_rem(b, v, x);
      }
      if (b != empty && c != empty) {
        contains_max(b);
        min_all(b, max(b));
        min_conj_rem(b, v, max(b));
      }
  }
}

lemma void contains_rem_max(bintree b)
  requires inorder(b) == true &*& b != empty &*& tree_rem(b, max(b)) != empty &*& inorder(tree_rem(b, max(b))) == true;
  ensures t_contains(b, max(tree_rem(b, max(b)))) == true;
{
  switch (b) {
    case empty:
    case tree(v, l, r):
      if (l == empty || r != empty) {
        if (tree_rem(r, max(r)) == empty) {
          min_le_max(r);
          contains_max(tree_rem(b, max(b)));
        } else {
          min_le_max(r);
          if (v != max(tree_rem(b, max(b)))) {
            max_all(tree_rem(b, max(b)), v);
          }
          contains_rem_max(r);
        }
      } else {
        contains_max(tree_rem(b, max(b)));
      }
  }
}

lemma void tree_rem_inorder(bintree b, int x)
  requires inorder(b) == true &*& t_contains(b, x) == true;
  ensures inorder(tree_rem(b, x)) == true &*& t_contains(tree_rem(b, x), x) == false;
{
  switch (b) {
    case empty:
    case tree(v, l, r):
      if (x < v) {
        max_conj_rem(l, v, x);
        tree_rem_inorder(l, x);
      }
      if (v < x) {
        min_conj_rem(r, v, x);
        tree_rem_inorder(r, x);
      }
      if (x == v) {
        if (l == empty && r != empty) {
          if (t_contains(r, x) == false) {
            contains_min(r);
          } else {
            min_all(r, x);
          }
        }
        if (r == empty && l != empty) {
          if (t_contains(l, x) == false) {
            contains_min(l);
          } else {
            max_all(l, x);
          }
        }
        if (r != empty && l != empty) {
          if (tree_rem(l, max(l)) != empty) {
            contains_max(l);
            tree_rem_inorder(l, max(l));
            contains_rem_max(l);
            if (max(l) != max(tree_rem(l, max(l)))) {
              max_all(l, max(tree_rem(l, max(l))));
              if (t_contains(r, x) == false) {
                contains_min(r);
              } else {
                min_all(r, x);
              }
            } else {
              contains_max(tree_rem(l, max(l)));
            }
          } else {
            if (t_contains(r, x) == false) {
              contains_min(r);
            } else {
              min_all(r, x);
            }
          }
        }
      }
  }
}
@*/

struct tree *init_tree(int x)
//@ requires true;
//@ ensures Tree(result, tree(x, empty, empty));
{
  struct tree *t = malloc(sizeof(struct tree));
  if(t!=0){
    t->value=x;
    t->left=0;
    t->right=0;
    //@ close Tree(0, empty);
    //@ close Tree(0, empty);
    //@ close Tree(t, tree(x, empty, empty));
    return t;
  }else{
	abort();
  }
}

void free_tree(struct tree *t)
//@ requires Tree(t, ?b);
//@ ensures true;
{
  if(t==0){
    //@ open Tree(t, b);
  }else{
    //@ open Tree(t, b);
    struct tree *l=t->left;
    struct tree *r=t->right;
    free_tree(l);
    free_tree(r);
    free(t);
  }
}

bool contains(struct tree *t,int x)
//@ requires Tree(t, ?b) &*& inorder(b) == true;
//@ ensures Tree(t, b) &*& result == t_contains(b, x) &*& inorder(b) == true;
{
  if(t==0){
    //@ open Tree(t, b);
    //@ close Tree(t, b);
    return false;
  }else{
    //@ open Tree(t, b);
    int v=t->value;
    struct tree *l=t->left;
    struct tree *r=t->right;
    if(v==x){
      //@ close Tree(t, b);
      return true;
    }else if(x < v){
      bool temp1=contains(l,x);
      //@ close Tree(t, b);
      return temp1;
    }else{
      bool temp2=contains(r,x);
      //@ close Tree(t, b);
      return temp2;
    }
  }
}

void add(struct tree *t, int x)
//@ requires Tree(t, ?b) &*& b != empty &*& inorder(b) == true &*& t_contains(b, x) == false;
//@ ensures Tree(t, tree_add(b, x)) &*& inorder(tree_add(b, x)) == true;
{
  //@ open Tree(t, b);
  int v=t->value;
  struct tree *l=t->left;
  //@ tree_add_inorder(b, x);
  struct tree *r=t->right;
  if(x < v){
    if(l!=0){
      add(l,x);
      //@ close Tree(t, tree_add(b, x));
    }else{
      struct tree *temp=init_tree(x);
      t->left=temp;
      //@ close Tree(t, tree_add(b, x));
    }
  }else{
    if(v < x){
      if(r!=0){
        add(r,x);
        //@ close Tree(t, tree_add(b, x));
      }else{
        struct tree *temp=init_tree(x);
        t->right=temp;
        //@ close Tree(t, tree_add(b, x));
      }
    } else {
      //@ close Tree(t, tree_add(b, x));
    }
  }
}

int maximum(struct tree *t)
//@ requires Tree(t, ?b) &*& b != empty &*& inorder(b) == true;
//@ ensures Tree(t, b) &*& result == max(b) &*& inorder(b) == true;
{
  //@ open Tree(t, b);
  int v=t->value;
  struct tree *r=t->right;
  if(r==0){
    //@ close Tree(t, b);
    return v;
  }else{
    int m= maximum(r);
    //@ close Tree(t, b);
    return m;
  }
}

struct tree* remove(struct tree *t, int x)
//@ requires Tree(t, ?b) &*& b != empty &*& inorder(b) == true &*& t_contains(b, x) == true;
//@ ensures Tree(result, tree_rem(b, x)) &*& inorder(tree_rem(b, x)) == true;
{
  //@ open Tree(t, b);
  //@ tree_rem_inorder(b, x);
  int v=t->value;
  struct tree *l=t->left;
  struct tree *r=t->right;
  if(x < v){
    if(l!=0){
      struct tree *temp=remove(l,x);
      t->left=temp;
      //@ close Tree(t, tree_rem(b, x));
      return t;
    }
  } else if(v < x){
    if(r!=0){
      struct tree *temp=remove(r,x);
      t->right=temp;
      //@ close Tree(t, tree_rem(b, x));
      return t;
    }
  } else {
    if (l == 0) {
      if (r == 0) {
        //@ open Tree(l, _);
        free_tree(t);
        //@ close Tree(0, empty);
        return 0;
      } else {
        //@ open Tree(l, _);
        free(t);
        return r;
      }
    } else {
      if(r==0){
        //@ open Tree(r, _);
        free(t);
        return l;
      } else {
        struct tree *temp=0;
        //@ contains_max(b);
        int m=maximum(l);
        t->value=m;
        temp=remove(l,m);
        t->left=temp;
        //@ close Tree(t, tree_rem(b, x));
        return t;
      }
    }
  }
  //@ close Tree(t, tree_rem(b, x));
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