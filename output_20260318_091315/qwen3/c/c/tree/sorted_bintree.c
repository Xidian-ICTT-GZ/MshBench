/*@ predicate tree(struct tree *t; int v, struct tree *l, struct tree *r) =
    t != 0 &*&
    t->value |-> v &*&
    t->left |-> l &*&
    t->right |-> r;
@*/

/*@ predicate tree_inorder(struct tree *t; list<int> vs) =
    t == 0 ?
        vs == nil
    :
        exists<int> v, struct tree *l, struct tree *r.
        tree(t, v, l, r) &*&
        tree_inorder(l, ?ls) &*&
        tree_inorder(r, ?rs) &*&
        vs == append(append(ls, cons(v, nil)), rs);
@*/

/*@ predicate tree_contains(struct tree *t, int x) =
    t == 0 ?
        false
    :
        exists<int> v, struct tree *l, struct tree *r.
        tree(t, v, l, r) &*&
        (v == x || tree_contains(l, x) || tree_contains(r, x));
@*/

/*@ predicate tree_max(struct tree *t, int m) =
    t == 0 ?
        false
    :
        exists<int> v, struct tree *l, struct tree *r.
        tree(t, v, l, r) &*&
        (r == 0 ?
            m == v
        :
            tree_max(r, m));
@*/

/*@ predicate tree_min(struct tree *t, int m) =
    t == 0 ?
        false
    :
        exists<int> v, struct tree *l, struct tree *r.
        tree(t, v, l, r) &*&
        (l == 0 ?
            m == v
        :
            tree_min(l, m));
@*/

//@ predicate valid_tree(struct tree *t) = tree_inorder(t, ?vs);

struct tree *init_tree(int x)
//@ requires true;
//@ ensures tree(result, x, 0, 0) &*& valid_tree(result);
{
  struct tree *t = malloc(sizeof(struct tree));
  if(t!=0){
    t->value=x;
    t->left=0;
    t->right=0;
    return t;
  }else{
	abort();
  }
}

void free_tree(struct tree *t)
//@ requires valid_tree(t);
//@ ensures true;
{
  if(t==0){
  }else{
    struct tree *l=t->left;
    struct tree *r=t->right;
    //@ open tree_inorder(t, _);
    free_tree(l);
    free_tree(r);
    free(t);
  }
}

bool contains(struct tree *t,int x)
//@ requires valid_tree(t);
//@ ensures valid_tree(t) &*& result == tree_contains(t, x);
{
  if(t==0){
    return false;
  }else{
    int v=t->value;
    struct tree *l=t->left;
    struct tree *r=t->right;
    //@ open tree_inorder(t, _);
    //@ open tree_contains(t, x);
    if(v==x){
      return true;
    }else if(x < v){
      bool temp1=contains(l,x);
      //@ close tree_inorder(t, _);
      return temp1;
    }else{
      bool temp2=contains(r,x);
      //@ close tree_inorder(t, _);
      return temp2;
    }
  }
}

void add(struct tree *t, int x)
//@ requires valid_tree(t) &*& !tree_contains(t, x);
//@ ensures valid_tree(t) &*& tree_contains(t, x);
{
  int v=t->value;
  struct tree *l=t->left;
  struct tree *r=t->right;
  //@ open tree_inorder(t, ?vs);
  if(x < v){
    if(l!=0){
      add(l,x);
      //@ close tree_inorder(t, vs);
    }else{
      struct tree *temp=init_tree(x);
      t->left=temp;
      //@ close tree_inorder(t, _);
    }
  }else{
    if(v < x){
      if(r!=0){
        add(r,x);
        //@ close tree_inorder(t, vs);
      }else{
        struct tree *temp=init_tree(x);
        t->right=temp;
        //@ close tree_inorder(t, _);
      }
    }
  }
}

int maximum(struct tree *t)
//@ requires valid_tree(t) &*& t != 0;
//@ ensures valid_tree(t) &*& tree_max(t, result);
{
  int v=t->value;
  struct tree *r=t->right;
  //@ open tree_inorder(t, _);
  if(r==0){
    return v;
  }else{
    int m= maximum(r);
    return m;
  }
}

struct tree* remove(struct tree *t, int x)
//@ requires valid_tree(t) &*& tree_contains(t, x);
//@ ensures valid_tree(result) &*& !tree_contains(result, x);
{
  int v=t->value;
  struct tree *l=t->left;
  struct tree *r=t->right;
  //@ open tree_inorder(t, ?vs);
  //@ open tree_contains(t, x);
  if(x < v){
    if(l!=0){
      struct tree *temp=remove(l,x);
      t->left=temp;
      //@ close tree_inorder(t, vs);
      return t;
    }
  } else if(v < x){
    if(r!=0){
      struct tree *temp=remove(r,x);
      t->right=temp;
      //@ close tree_inorder(t, vs);
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
        //@ close tree_inorder(t, _);
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
  //@ close valid_tree(t1);

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