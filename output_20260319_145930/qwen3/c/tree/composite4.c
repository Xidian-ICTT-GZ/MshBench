//@ #include "stdlib.gh"

/*@ predicate node(struct node *n; struct node *left, struct node *right, struct node *parent, int count) =
    n != 0 &*&
    malloc_block_node(n) &*&
    n->left |-> left &*&
    n->right |-> right &*&
    n->parent |-> parent &*&
    n->count |-> count;
@*/

/*@ predicate tree(struct node *root) =
    root == 0 ?
        true
    :
        node(root, ?l, ?r, ?p, ?c) &*&
        tree(l) &*& tree(r) &*&
        (l != 0 ==> node(l, _, _, root, _)) &*&
        (r != 0 ==> node(r, _, _, root, _));
@*/

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

struct node * create_node(struct node * p)
//@ requires true;
//@ ensures node(result, 0, 0, p, 1);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0; 
  n->right = 0; 
  n->parent = p;
  n->count = 1;
  //@ close node(n, 0, 0, p, 1);
  return n;
}

struct node *create_tree()
//@ requires true;
//@ ensures tree(result);
{
  struct node *n = create_node(0);
  //@ close tree(n);
  return n;
}

int subtree_get_count(struct node *node)
//@ requires tree(node);
//@ ensures tree(node) &*& result == (node == 0 ? 0 : node->count);
{
  int result = 0;
  
  if (node != 0) {
    //@ open tree(node);
    //@ assert node(node, ?l, ?r, ?p, ?c);
    result = node->count;
    //@ close tree(node);
  }
  
  
  return result;
}

void fixup_ancestors(struct node * n, struct node * p, int count)
//@ requires

//@ ensures

{
  
  if (p == 0) {
  } else {
    //@ open node(p, ?left, ?right, ?grandparent, _);
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
      leftCount = count;
      rightCount = subtree_get_count(right);
    } else {
      leftCount = subtree_get_count(left);
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      //@ close node(p, left, right, grandparent, pcount);
      fixup_ancestors(p, grandparent, pcount);
    }
  }
  
}

struct node *tree_add_left(struct node *node)
//@ requires tree(node) &*& node != 0;
//@ ensures tree(node) &*& tree(result) &*& result->parent == node;
{
  
  struct node *n = create_node(node);
  //@ open tree(node);
  //@ assert node(node, ?oldLeft, ?oldRight, ?par, ?cnt);
  {
      struct node *nodeLeft = node->left;
      
      node->left = n;
      //@ close node(node, n, oldRight, par, _);

      //@ close tree(n);
      //@ close tree(oldLeft);
      //@ close tree(oldRight);
      //@ close tree(node);
      
      fixup_ancestors(n, node, 1);
      
  }
  

  return n;
}

struct node *tree_add_right(struct node *node)
//@ requires tree(node) &*& node != 0;
//@ ensures tree(node) &*& tree(result) &*& result->parent == node;
{
    
    struct node *n = create_node(node);
    //@ open tree(node);
    //@ assert node(node, ?oldLeft, ?oldRight, ?par, ?cnt);
    {
        struct node *nodeRight = node->right;
        
        node->right = n;
        //@ close node(node, oldLeft, n, par, _);

        //@ close tree(n);
        //@ close tree(oldLeft);
        //@ close tree(oldRight);
        //@ close tree(node);
        
        fixup_ancestors(n, node, 1);
        
    }
    
    return n;
}

struct node *tree_get_parent(struct node *node)
//@ requires tree(?root) &*& node != 0 &*& node_in_tree(node, root);
//@ ensures tree(root) &*& result == node->parent;
{
  
  
  struct node *p = node->parent;
  
  
  
  

  
  
  return p;
}

/*@ predicate node_in_tree(struct node *n, struct node *root) =
    n == root ?
        true
    :
        root != 0 &*&
        node(root, ?l, ?r, _, _) &*&
        (node_in_tree(n, l) || node_in_tree(n, r));
@*/

void subtree_dispose(struct node *node)
//@ requires tree(node);
//@ ensures true;
{
  
  if (node != 0) {
    //@ open tree(node);
    //@ assert node(node, ?l, ?r, _, _);
    {
      struct node *left = node->left;
      subtree_dispose(left);
    }
    {
      struct node *right = node->right;
      subtree_dispose(right);
    }
    free(node);
  }
}

void tree_dispose(struct node *node)
//@ requires tree(node);
//@ ensures true;
{
  
  
  subtree_dispose(node);
}

int main0()
//@ requires true;
//@ ensures true;
{
  struct node *node = create_tree();
  node = tree_add_left(node);
  node = tree_add_right(node);
  node = tree_get_parent(node);
  node = tree_add_left(node);
  node = tree_get_parent(node);
  node = tree_get_parent(node);
  tree_dispose(node);
  return 0;
}

int main() 
//@ requires true;
//@ ensures true;
{
    struct node *root = create_tree();
    struct node *left = tree_add_left(root);
    struct node *leftRight = tree_add_right(left);
    struct node *leftRightParent = tree_get_parent(leftRight);
    
    struct node *leftLeft = tree_add_left(left);
    
    struct node *leftRightRight = tree_add_right(leftRight);
    
    
    tree_dispose(root);
    return 0;
}