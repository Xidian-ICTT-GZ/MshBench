/*@ predicate tree(struct node *node; struct node *parent, int count) =
    node == 0 ?
        count == 0
    :
        malloc_block_node(node) &*&
        tree(node->left, node, ?leftCount) &*&
        tree(node->right, node, ?rightCount) &*&
        node->parent |-> parent &*&
        node->count |-> count &*&
        count == 1 + leftCount + rightCount;
@*/

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

struct node * create_node(struct node * p)
//@ requires true;
//@ ensures tree(result, p, 1);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0; 
  n->right = 0; 
  n->parent = p;
  n->count = 1;
  //@ close tree(n, p, 1);
  return n;
}

struct node *create_tree()
//@ requires true;
//@ ensures tree(result, 0, 1);
{
  struct node *n = create_node(0);
  return n;
}

int subtree_get_count(struct node *node)
//@ requires tree(node, ?parent, ?count);
//@ ensures tree(node, parent, count) &*& result == count;
{
  int result = 0;
  if (node != 0) { 
    //@ open tree(node, parent, count);
    result = node->count;
    //@ close tree(node, parent, count);
  }
  return result;
}

void fixup_ancestors(struct node * n, struct node * p, int count)
//@ requires tree(n, p, count) &*& tree(p, ?grandparent, ?oldPCount);
//@ ensures tree(n, p, count) &*& tree(p, grandparent, ?newPCount);
{
  if (p == 0) {
  } else {
    //@ open tree(p, grandparent, oldPCount);
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
      //@ open tree(left, p, _);
      leftCount = count;
      //@ close tree(left, p, count);
      rightCount = subtree_get_count(right);
    } else {
      leftCount = subtree_get_count(left);
      //@ open tree(right, p, _);
      rightCount = count;
      //@ close tree(right, p, count);
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      //@ close tree(p, grandparent, pcount);
      fixup_ancestors(p, grandparent, pcount);
    }
  }
}

struct node *tree_add_left(struct node *node)
//@ requires tree(node, ?parent, ?count);
//@ ensures tree(node, parent, ?newCount) &*& tree(result, node, 1) &*& newCount == count + 1;
{
  struct node *n = create_node(node);
  {
      struct node *nodeLeft = node->left;
      //@ open tree(node, parent, count);
      node->left = n;
      //@ close tree(node, parent, count + 1);
      fixup_ancestors(n, node, 1);
  }
  return n;
}

struct node *tree_add_right(struct node *node)
//@ requires tree(node, ?parent, ?count);
//@ ensures tree(node, parent, ?newCount) &*& tree(result, node, 1) &*& newCount == count + 1;
{
    struct node *n = create_node(node);
    {
        struct node *nodeRight = node->right;
        //@ open tree(node, parent, count);
        node->right = n;
        //@ close tree(node, parent, count + 1);
        fixup_ancestors(n, node, 1);
    }
    return n;
}

struct node *tree_get_parent(struct node *node)
//@ requires tree(node, ?parent, ?count);
//@ ensures tree(node, parent, count) &*& result == parent;
{
  struct node *p = node->parent;
  return p;
}

void subtree_dispose(struct node *node)
//@ requires tree(node, ?parent, ?count);
//@ ensures true;
{
  if (node != 0) {
    //@ open tree(node, parent, count);
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
//@ requires tree(node, 0, ?count);
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