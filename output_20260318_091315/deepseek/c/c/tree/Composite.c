/*@
predicate node(struct Node* n; struct Node* parent, struct Node* left, struct Node* right, int count) =
    n != 0 &*&
    n->left |-> left &*&
    n->right |-> right &*&
    n->parent |-> parent &*&
    n->count |-> count &*&
    malloc_block_Node(n);
@*/

/*@
predicate tree(struct Node* n) =
    n == 0 ? true : node(n, ?parent, ?left, ?right, ?count) &*& tree(left) &*& tree(right);
@*/

/*@
lemma void tree_count_nonnegative(struct Node* n)
requires tree(n);
ensures tree(n);
{
    open tree(n);
    if (n != 0) {
        open node(n, ?parent, ?left, ?right, ?count);
        tree_count_nonnegative(left);
        tree_count_nonnegative(right);
        close node(n, parent, left, right, count);
    }
    close tree(n);
}
@*/

int main() 
//@ requires true;
//@ ensures true;
{
  struct Node* mytree = create();
  struct Node* child = addLeft(mytree);
  
  struct Node* child2 = addLeft(child);
  
  int c = getNbOfNodes(child2);
  //@ assert c == 1;
  abort();
}

struct Node* create() 
//@ requires true;
//@ ensures node(result, 0, 0, 0, 1);
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
  return n;
}

struct Node* addLeft(struct Node* node)
//@ requires node(node, ?parent, ?left, ?right, ?count) &*& left == 0;
//@ ensures node(node, parent, result, right, count + 1) &*& node(result, node, 0, 0, 1);
{
  //@ open node(node, parent, left, right, count);
  struct Node* newChild = internalAddLeft(node);
  //@ close node(node, parent, newChild, right, count + 1);
  return newChild;
}

int getNbOfNodes(struct Node* n)
//@ requires node(n, ?parent, ?left, ?right, ?count);
//@ ensures node(n, parent, left, right, count) &*& result == count;
{
    //@ open node(n, parent, left, right, count);
    int c = internalGetNbOfNodes(n);
    //@ close node(n, parent, left, right, count);
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
//@ ensures node(result, parent, 0, 0, 1);
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  //@ close node(n, parent, 0, 0, 1);
  return n;
}

struct Node* internalAddLeft(struct Node* node)
//@ requires node(node, ?parent, ?left, ?right, ?count) &*& left == 0;
//@ ensures node(node, parent, result, right, count + 1) &*& node(result, node, 0, 0, 1);
{
    //@ open node(node, parent, left, right, count);
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    //@ close node(node, parent, child, right, count + 1);
    return child;
}

void fix(struct Node* node)
//@ requires node(node, ?parent, ?left, ?right, ?count) &*& count < INT_MAX;
//@ ensures node(node, parent, left, right, count + 1);
{
  //@ open node(node, parent, left, right, count);
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  //@ close node(node, parent, left, right, count + 1);
  struct Node* parent = node->parent;
  if(parent==0){
  } else {
    //@ open node(parent, ?grandparent, ?parentLeft, ?parentRight, ?parentCount);
    //@ assert parentLeft == node || parentRight == node;
    //@ close node(parent, grandparent, parentLeft, parentRight, parentCount);
    fix(parent);
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
//@ requires node(n, ?parent, ?left, ?right, ?count);
//@ ensures node(n, parent, left, right, count) &*& result == count;
{
  //@ open node(n, parent, left, right, count);
  int c = n->count;
  //@ close node(n, parent, left, right, count);
  return c;
}