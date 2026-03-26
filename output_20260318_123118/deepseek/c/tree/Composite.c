/*@
predicate node(struct Node* n; struct Node* left, struct Node* right, struct Node* parent, int count) =
    n != 0 &*&
    n->left |-> left &*&
    n->right |-> right &*&
    n->parent |-> parent &*&
    n->count |-> count &*&
    malloc_block_Node(n);
@*/

/*@
predicate tree(struct Node* n) =
    n == 0 ?
        true
    :
        node(n, ?left, ?right, ?parent, ?count) &*&
        tree(left) &*&
        tree(right);
@*/

/*@
lemma void tree_count_nonnegative(struct Node* n)
requires tree(n);
ensures tree(n);
{
    open tree(n);
    if (n != 0) {
        open node(n, ?left, ?right, ?parent, ?count);
        tree_count_nonnegative(left);
        tree_count_nonnegative(right);
        close node(n, left, right, parent, count);
    }
    close tree(n);
}
@*/

int main() 
//@ requires true;
//@ ensures true;
{
  struct Node* mytree = create();
  //@ assert tree(mytree);
  struct Node* child = addLeft(mytree);
  //@ assert tree(mytree);
  //@ assert tree(child);
  
  struct Node* child2 = addLeft(child);
  //@ assert tree(mytree);
  //@ assert tree(child);
  //@ assert tree(child2);
  
  int c = getNbOfNodes(child2);
  //@ assert tree(child2);
  //@ tree_count_nonnegative(child2);
  assert(c==1);
  abort();
  return 0;
}

struct Node* create() 
//@ requires true;
//@ ensures tree(result);
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0){
    abort();
  } else {
  }
  n->parent = 0;
  n->left = 0;
  n->right = 0;
  n->count = 1;
  //@ close node(n, 0, 0, 0, 1);
  //@ close tree(n);
  return n;
}

struct Node* addLeft(struct Node* node)
//@ requires tree(node);
//@ ensures tree(node) &*& tree(result);
{
  //@ open tree(node);
  //@ open node(node, ?left, ?right, ?parent, ?count);
  struct Node* newChild = internalAddLeft(node);
  //@ close node(node, newChild, right, parent, count + 1);
  //@ close tree(node);
  //@ close tree(newChild);
  return newChild;
}

int getNbOfNodes(struct Node* n)
//@ requires tree(n);
//@ ensures tree(n);
{
    //@ open tree(n);
    //@ open node(n, ?left, ?right, ?parent, ?count);
    int c = internalGetNbOfNodes(n);
    //@ close node(n, left, right, parent, count);
    //@ close tree(n);
    return c;
}

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

struct Node* internalCreate(struct Node* parent)
//@ requires true;
//@ ensures node(result, 0, 0, parent, 1);
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  //@ close node(n, 0, 0, parent, 1);
  return n;
}

struct Node* internalAddLeft(struct Node* node)
//@ requires node(node, ?left, ?right, ?parent, ?count);
//@ ensures node(node, result, right, parent, count + 1) &*& node(result, 0, 0, node, 1);
{
    //@ open node(node, left, right, parent, count);
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    //@ close node(node, child, right, parent, count + 1);
    return child;
}

void fix(struct Node* node)
//@ requires node(node, ?left, ?right, ?parent, ?count);
//@ ensures node(node, left, right, parent, count + 1);
{
  //@ open node(node, left, right, parent, count);
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  //@ close node(node, left, right, parent, count + 1);
  struct Node* parent = node->parent;
  if(parent==0){
  } else {
    //@ open node(parent, ?p_left, ?p_right, ?p_parent, ?p_count);
    fix(parent);
    //@ close node(parent, p_left, p_right, p_parent, p_count + 1);
  }
}

void abort()
//@ requires true;
//@ ensures false;
{
  while(true)
  //@ invariant true;
  {
  }
}

int internalGetNbOfNodes(struct Node* n)
//@ requires node(n, ?left, ?right, ?parent, ?count);
//@ ensures node(n, left, right, parent, count) &*& result == count;
{
  //@ open node(n, left, right, parent, count);
  int c = n->count;
  //@ close node(n, left, right, parent, count);
  return c;
}