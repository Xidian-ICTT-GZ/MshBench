#include <stdlib.h>
#include <limits.h>

struct Node
{
  struct Node *left;
  struct Node *right;
  struct Node *parent;
  int count;
};

/*@ predicate node(struct Node *n) = n->left |-> _ &*& n->right |-> _ &*& n->parent |-> _ &*& n->count |-> _; @*/

struct Node *create()
/*@ requires emp; @*/
/*@ ensures node(result) &*& result->parent |-> 0 &*& result->left |-> 0 &*& result->right |-> 0 &*& result->count |-> 1; @*/
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

struct Node *internalCreate(struct Node *parent)
/*@ requires node(parent); @*/
/*@ ensures node(result) &*& result->parent |-> parent &*& result->left |-> 0 &*& result->right |-> 0 &*& result->count |-> 1 &*& node(parent); @*/
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

void fix(struct Node *node)
/*@ requires node(node); @*/
/*@ ensures node(node); @*/
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

struct Node *internalAddLeft(struct Node *node)
/*@ requires node(node); @*/
/*@ ensures node(result) &*& node(node); @*/
{
  struct Node *child = internalCreate(node);
  node->left = child;
  fix(node);
  return child;
}

struct Node *addLeft(struct Node *node)
/*@ requires node(node); @*/
/*@ ensures node(result) &*& node(node); @*/
{
  struct Node *newChild = internalAddLeft(node);
  return newChild;
}

int internalGetNbOfNodes(struct Node *n)
/*@ requires node(n); @*/
/*@ ensures node(n); @*/
{
  int c = n->count;
  return c;
}

int getNbOfNodes(struct Node *n)
/*@ requires node(n); @*/
/*@ ensures node(n); @*/
{
  int c = internalGetNbOfNodes(n);
  return c;
}

void abort()
/*@ requires emp; @*/
/*@ ensures false; @*/
{
  while (true)
  {
  }
}

int main()
/*@ requires emp; @*/
/*@ ensures false; @*/
{
  struct Node *mytree = create();
  struct Node *child = addLeft(mytree);
  struct Node *child2 = addLeft(child);
  int c = getNbOfNodes(child2);
  assert(c == 1);
  abort();
}