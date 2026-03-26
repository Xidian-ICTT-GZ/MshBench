#include "stdlib.h"
#include "limits.h"
#include "assert.h"

/*@

predicate node(struct Node *n; struct Node *left, struct Node *right, struct Node *parent, int count) =
  n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count;

@*/

struct Node;
struct Node *create();
struct Node *addLeft(struct Node *node);
int getNbOfNodes(struct Node *n);
struct Node *internalCreate(struct Node *parent);
struct Node *internalAddLeft(struct Node *node);
void fix(struct Node *node);
void abort();
int internalGetNbOfNodes(struct Node *n);

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

  return n;
}

struct Node *addLeft(struct Node *node)

//@ requires node(node, ?l, ?r, ?p, ?c);
//@ ensures node(node, result, r, p, c + 1) &*& node(result, 0, 0, node, 1);
{

  struct Node *newChild = internalAddLeft(node);

  return newChild;
}

int getNbOfNodes(struct Node *n)

//@ requires node(n, ?l, ?r, ?p, ?c);
//@ ensures node(n, l, r, p, c) &*& result == c;
{

  int c = internalGetNbOfNodes(n);

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
//@ ensures node(result, 0, 0, parent, 1);
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

//@ requires node(node, ?l, ?r, ?p, ?c) &*& c < INT_MAX;
//@ ensures node(node, result, r, p, c + 1) &*& node(result, 0, 0, node, 1);
{
  struct Node *child = internalCreate(node);
  node->left = child;
  fix(node);
  return child;
}

void fix(struct Node *node)

//@ requires node(node, ?l, ?r, ?p, ?c) &*& c < INT_MAX;
//@ ensures node(node, l, r, p, c + 1);
{

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
    fix(parent);
  }
}

void abort()

//@ requires true;
//@ ensures false;
{
  while (true)

  //@ invariant true == false;
  {
  }
}

int internalGetNbOfNodes(struct Node *n)

//@ requires node(n, ?l, ?r, ?p, ?c);
//@ ensures node(n, l, r, p, c) &*& result == c;
{

  int c = n->count;

  return c;
}