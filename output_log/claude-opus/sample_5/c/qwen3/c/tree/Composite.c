#include <stdlib.h>
#include <limits.h>

struct Node
{
  struct Node *left;
  struct Node *right;
  struct Node *parent;
  int count;
};

/*@ predicate node(struct Node *n; int count, struct Node *parent, struct Node *left, struct Node *right) =
    n != 0 &*&
    malloc_block_Node(n) &*&
    n->count |-> count &*&
    n->parent |-> parent &*&
    n->left |-> left &*&
    n->right |-> right;
@*/

/*@
lemma void tree_validity(struct Node *n)
    requires node(n, ?c, ?p, ?l, ?r) &*& c > 0;
    ensures node(n, c, p, l, r);
{
}
@*/

void abort();
    //@ requires true;
    //@ ensures false;

struct Node *internalCreate(struct Node *parent);
    //@ requires true;
    //@ ensures node(result, 1, parent, 0, 0);

void fix(struct Node *node);
    //@ requires node(node, ?c, ?p, ?l, ?r) &*& c >= 1 &*& c < INT_MAX;
    //@ ensures node(node, c + 1, p, l, r);

struct Node *internalAddLeft(struct Node *node);
    //@ requires node(node, ?c, ?p, ?l, ?r) &*& c >= 1 &*& c < INT_MAX;
    //@ ensures node(result, 1, node, 0, 0) &*& node(node, c + 1, p, result, r);

int internalGetNbOfNodes(struct Node *n);
    //@ requires node(n, ?c, ?p, ?l, ?r);
    //@ ensures node(n, c, p, l, r) &*& result == c;

struct Node *create()
    //@ requires true;
    //@ ensures node(result, 1, 0, 0, 0);
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

  return n;
}

struct Node *addLeft(struct Node *node)
    //@ requires node(node, ?c, ?p, ?l, ?r) &*& c >= 1 &*& c < INT_MAX;
    //@ ensures node(result, 1, node, 0, 0) &*& node(node, c + 1, p, result, r);
{

  struct Node *newChild = internalAddLeft(node);

  return newChild;
}

int getNbOfNodes(struct Node *n)
    //@ requires node(n, ?c, ?p, ?l, ?r);
    //@ ensures node(n, c, p, l, r) &*& result == c;
{

  int c = internalGetNbOfNodes(n);

  return c;
}

struct Node *internalCreate(struct Node *parent)
    //@ requires true;
    //@ ensures node(result, 1, parent, 0, 0);
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

  return n;
}

struct Node *internalAddLeft(struct Node *node)
    //@ requires node(node, ?c, ?p, ?l, ?r) &*& c >= 1 &*& c < INT_MAX;
    //@ ensures node(result, 1, node, 0, 0) &*& node(node, c + 1, p, result, r);
{
  //@ open node(node, c, p, l, r);
  struct Node *child = internalCreate(node);
  node->left = child;
  //@ close node(node, c, p, child, r);
  fix(node);
  return child;
}

void fix(struct Node *node)
    //@ requires node(node, ?c, ?p, ?l, ?r) &*& c >= 1 &*& c < INT_MAX;
    //@ ensures node(node, c + 1, p, l, r);
{
  //@ open node(node, c, p, l, r);
  int tmp = node->count;
  if (tmp == INT_MAX)
  {
    abort();
  }
  node->count = tmp + 1;

  struct Node *parent = node->parent;
  if (parent == 0)
  {
  }
  else
  {
  }
  //@ close node(node, c + 1, p, l, r);
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
    //@ requires node(n, ?c, ?p, ?l, ?r);
    //@ ensures node(n, c, p, l, r) &*& result == c;
{
  //@ open node(n, c, p, l, r);
  int c = n->count;
  //@ close node(n, c, p, l, r);
  return c;
}

int main()
    //@ requires true;
    //@ ensures true;
{
  struct Node *mytree = create();
  struct Node *child = addLeft(mytree);

  struct Node *child2 = addLeft(child);

  int c = getNbOfNodes(child2);
  assert(c == 1);
  abort();
}