/*@
predicate tree(struct tree *t; int v, struct tree *l, struct tree *r) =
  t != 0 &*&
  t->value |-> v &*&
  t->left |-> l &*&
  t->right |-> r;

predicate tree_inorder(struct tree *t, list<int> vs) =
  t == 0 ?
    vs == nil
  :
    exists(v, l, r, ls, rs).
      tree(t, v, l, r) &*&
      tree_inorder(l, ls) &*&
      tree_inorder(r, rs) &*&
      vs == append(ls, cons(v, rs)) &*&
      forall(ls, (geq)(v)) == true &*&
      forall(rs, (leq)(v)) == true;

lemma void append_nil(list<int> xs)
  requires true;
  ensures append(xs, nil) == xs;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      append_nil(t);
  }
}

lemma void forall_geq_leq_trans(int x, list<int> xs, list<int> ys)
  requires
    forall(xs, (geq)(x)) == true &*&
    forall(ys, (leq)(x)) == true;
  ensures
    forall(xs, (geq)(y)) == true &*&
    forall(ys, (leq)(z)) == true
    for some y, z;
{
}

lemma void tree_inorder_contains(struct tree *t, list<int> vs, int x)
  requires tree_inorder(t, vs) &*& mem(x, vs) == true;
  ensures tree_inorder(t, vs) &*& contains(t, x) == true;
{
  if (t == 0) {
  } else {
    open tree_inorder(t, vs);
    assert tree(t, ?v, ?l, ?r);
    assert tree_inorder(l, ?ls);
    assert tree_inorder(r, ?rs);
    if (mem(x, ls) == true) {
      tree_inorder_contains(l, ls, x);
    } else if (x == v) {
    } else {
      assert mem(x, rs) == true;
      tree_inorder_contains(r, rs, x);
    }
    close tree_inorder(t, vs);
  }
}

lemma void contains_tree_inorder(struct tree *t, list<int> vs, int x)
  requires tree_inorder(t, vs) &*& contains(t, x) == true;
  ensures tree_inorder(t, vs) &*& mem(x, vs) == true;
{
  if (t == 0) {
  } else {
    open tree_inorder(t, vs);
    assert tree(t, ?v, ?l, ?r);
    assert tree_inorder(l, ?ls);
    assert tree_inorder(r, ?rs);
    if (x == v) {
    } else if (x < v) {
      contains_tree_inorder(l, ls, x);
    } else {
      contains_tree_inorder(r, rs, x);
    }
    close tree_inorder(t, vs);
  }
}
@*/

struct tree *init_tree(int x)
//@ requires true;
//@ ensures tree_inorder(result, cons(x, nil));
{
  struct tree *t = malloc(sizeof(struct tree));
  if(t!=0){
    t->value=x;
    t->left=0;
    t->right=0;
    //@ close tree(t, x, 0, 0);
    //@ close tree_inorder(t, cons(x, nil));
    return t;
  }else{
	abort();
  }
}

void free_tree(struct tree *t)
//@ requires tree_inorder(t, ?vs);
//@ ensures true;
{
  if(t==0){
    
  }else{
    //@ open tree_inorder(t, vs);
    //@ open tree(t, ?v, ?l, ?r);
    struct tree *l=t->left;
    struct tree *r=t->right;
    free_tree(l);
    free_tree(r);
    free(t);
  }
}

bool contains(struct tree *t,int x)
//@ requires tree_inorder(t, ?vs);
//@ ensures tree_inorder(t, vs) &*& result == mem(x, vs);
{
  if(t==0){
    return false;
  }else{
    //@ open tree_inorder(t, vs);
    //@ open tree(t, ?v, ?l, ?r);
    int v=t->value;
    struct tree *l=t->left;
    struct tree *r=t->right;
    if(v==x){
      //@ close tree(t, v, l, r);
      //@ close tree_inorder(t, vs);
      return true;
    }else if(x < v){
      bool temp1=contains(l,x);
      //@ close tree(t, v, l, r);
      //@ close tree_inorder(t, vs);
      return temp1;
    }else{
      bool temp2=contains(r,x);
      //@ close tree(t, v, l, r);
      //@ close tree_inorder(t, vs);
      return temp2;
    }
  }
}

void add(struct tree *t, int x)
//@ requires tree_inorder(t, ?vs) &*& mem(x, vs) == false;
//@ ensures tree_inorder(t, ?vs1) &*& mem(x, vs1) == true;
{
  //@ open tree_inorder(t, vs);
  //@ open tree(t, ?v, ?l, ?r);
  int v=t->value;
  struct tree *l=t->left;
  struct tree *r=t->right;
  if(x < v){
    if(l!=0){
      add(l,x);
      //@ close tree(t, v, l, r);
      //@ close tree_inorder(t, _);
    }else{
      struct tree *temp=init_tree(x);
      t->left=temp;
      //@ close tree(t, v, temp, r);
      //@ close tree_inorder(t, _);
    }
  }else{
    if(v < x){
      if(r!=0){
        add(r,x);
        //@ close tree(t, v, l, r);
        //@ close tree_inorder(t, _);
      }else{
        struct tree *temp=init_tree(x);
        t->right=temp;
        //@ close tree(t, v, l, temp);
        //@ close tree_inorder(t, _);
      }
    }
  }
}

int maximum(struct tree *t)
//@ requires tree_inorder(t, ?vs) &*& vs != nil;
//@ ensures tree_inorder(t, vs) &*& result == last(vs);
{
  //@ open tree_inorder(t, vs);
  //@ open tree(t, ?v, ?l, ?r);
  int v=t->value;
  struct tree *r=t->right;
  if(r==0){
    //@ close tree(t, v, l, r);
    //@ close tree_inorder(t, vs);
    return v;
  }else{
    int m= maximum(r);
    //@ close tree(t, v, l, r);
    //@ close tree_inorder(t, vs);
    return m;
  }
}

struct tree* remove(struct tree *t, int x)
//@ requires tree_inorder(t, ?vs) &*& mem(x, vs) == true;
//@ ensures tree_inorder(result, ?vs1) &*& mem(x, vs1) == false;
{
  //@ open tree_inorder(t, vs);
  //@ open tree(t, ?v, ?l, ?r);
  int v=t->value;
  struct tree *l=t->left;
  struct tree *r=t->right;
  if(x < v){
    if(l!=0){
      struct tree *temp=remove(l,x);
      t->left=temp;
      //@ close tree(t, v, temp, r);
      //@ close tree_inorder(t, _);
      return t;
    }
  } else if(v < x){
    if(r!=0){
      struct tree *temp=remove(r,x);
      t->right=temp;
      //@ close tree(t, v, l, temp);
      //@ close tree_inorder(t, _);
      return t;
    }
  } else {
    if (l == 0) {
      if (r == 0) {
        free_tree(t);
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
        //@ close tree_inorder(t, _);
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