/*@
predicate node(struct Node *n; struct Node *parent, struct Node *left, struct Node *right, int count) =
    n->parent |-> parent &*& n->left |-> left &*& n->right |-> right &*& n->count |-> count &*& malloc_block_Node(n);
@*/

int main()
//@ requires true;
//@ ensures true;
{
  struct Node *mytree = create();
  //@ assert node(mytree, 0, 0, 0, 1);
  struct Node *child = addLeft(mytree);
  //@ assert node(child, mytree, 0, 0, 1);
  //@ assert node(mytree, 0, child, 0, 2);

  struct Node *child2 = addLeft(child);
  //@ assert node(child2, child, 0, 0, 1);
  //@ assert node(child, mytree, child2, 0, 2);
  //@ assert node(mytree, 0, child, 0, 3);

  int c = getNbOfNodes(child2);
  //@ assert c == 1;
  assert(c == 1);
  abort();
}

struct Node *create()
//@ requires true;
//@ ensures node(result, 0, 0, 0, 1);
{
  struct Node *n = malloc(sizeof(struct Node));
  if (n == 0)
  {
    abort();
  }
  else
  {
  }
  n->parent = 0;
  n->left = 0;
  n->right = 0;
  n->count = 1;
  //@ close node(n, 0, 0, 0, 1);
  return n;
}

struct Node *addLeft(struct Node *node)
//@ requires node(node, ?parent, ?left, ?right, ?count);
//@ ensures node(result, node, 0, 0, 1) &*& node(node, parent, result, right, count + 1);
{
  //@ open node(node, parent, left, right, count);
  struct Node *newChild = internalAddLeft(node);
  //@ close node(node, parent, newChild, right, count + 1);
  return newChild;
}

int getNbOfNodes(struct Node *n)
//@ requires node(n, ?parent, ?left, ?right, ?count);
//@ ensures node(n, parent, left, right, count) &*& result == count;
{
  //@ open node(n, parent, left, right, count);
  int c = internalGetNbOfNodes(n);
  //@ close node(n, parent, left, right, count);
  return c;
}

struct Node
{
  struct Node *left;
  struct Node *right;
  struct Node *parent;
  int count;
};

struct Node *internalCreate(struct Node *parent)
//@ requires true;
//@ ensures node(result, parent, 0, 0, 1);
{
  struct Node *n = malloc(sizeof(struct Node));
  if (n == 0)
  {
    abort();
  }
  else
  {
  }
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  //@ close node(n, parent, 0, 0, 1);
  return n;
}

struct Node *internalAddLeft(struct Node *node)
//@ requires node(node, ?parent, ?left, ?right, ?count);
//@ ensures node(result, node, 0, 0, 1) &*& node(node, parent, result, right, count + 1);
{
  //@ open node(node, parent, left, right, count);
  struct Node *child = internalCreate(node);
  node->left = child;
  fix(node);
  //@ close node(node, parent, child, right, count + 1);
  return child;
}

void fix(struct Node *node)
//@ requires node(node, ?parent, ?left, ?right, ?count);
//@ ensures node(node, parent, left, right, count + 1);
{
  //@ open node(node, parent, left, right, count);
  int tmp = node->count;
  if (tmp == INT_MAX)
  {
    abort();
  }
  node->count = tmp + 1;
  //@ close node(node, parent, left, right, count + 1);
  struct Node *parent = node->parent;
  if (parent == 0)
  {
  }
  else
  {
    //@ open node(parent, ?grandparent, ?parentLeft, ?parentRight, ?parentCount);
    fix(parent);
    //@ close node(parent, grandparent, parentLeft, parentRight, parentCount + 1);
  }
}

void abort()
//@ requires true;
//@ ensures false;
{
  while (true)
  //@ invariant true;
  {
  }
}

int internalGetNbOfNodes(struct Node *n)
//@ requires node(n, ?parent, ?left, ?right, ?count);
//@ ensures node(n, parent, left, right, count) &*& result == count;
{
  //@ open node(n, parent, left, right, count);
  int c = n->count;
  //@ close node(n, parent, left, right, count);
  return c;
}