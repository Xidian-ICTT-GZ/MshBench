#include <limits.h>
#include <stdbool.h>
#include <stdlib.h>

struct Node
{
  struct Node *left;
  struct Node *right;
  struct Node *parent;
  int count;
};

/*@
predicate node(struct Node *n; struct Node *p, int cnt) =
  n->left |-> _ &*& n->right |-> _ &*& n->parent |-> p &*& n->count |-> cnt &*& malloc_block_Node(n);
@*/

/*@
predicate node_with_left(struct Node *n; struct Node *p, struct Node *l, int cnt) =
  n->left |-> l &*& n->right |-> _ &*& n->parent |-> p &*& n->count |-> cnt &*& malloc_block_Node(n);
@*/

//@ requires true;
//@ ensures false;
void abort()
{
  while (true)
  {
  }
}

//@ requires true;
//@ ensures node(result, 0, 1);
struct Node *create()
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
  //@ close node(n, 0, 1);
  return n;
}

//@ requires node(parent, _, _);
//@ ensures node(result, parent, 1);
struct Node *internalCreate(struct Node *parent)
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
  //@ close node(n, parent, 1);
  return n;
}

//@ requires node(node, p, c) &*& c < INT_MAX;
//@ ensures node(node, p, c + 1);
void fix(struct Node *node)
{
  //@ open node(node, p, c);
  int tmp = node->count;
  if (tmp == INT_MAX)
  {
    abort();
  }
  node->count = tmp + 1;

  struct Node *parent = node->parent;
  if (parent == 0)
  {
    //@ close node(node, 0, tmp + 1);
  }
  else
  {
    //@ close node(node, parent, tmp + 1);
    fix(parent);
  }
}

//@ requires node(node, p, c) &*& c < INT_MAX;
//@ ensures node_with_left(node, p, result, c + 1) &*& node(result, node, 1);
struct Node *internalAddLeft(struct Node *node)
{
  struct Node *child = internalCreate(node);
  //@ open node(node, p, c);
  node->left = child;
  //@ close node_with_left(node, p, child, c);
  //@ open node_with_left(node, p, child, c);
  //@ close node(node, p, c);
  fix(node);
  return child;
}

//@ requires node(node, p, c) &*& c < INT_MAX;
//@ ensures node_with_left(node, p, result, c + 1) &*& node(result, node, 1);
struct Node *addLeft(struct Node *node)
{
  struct Node *newChild = internalAddLeft(node);
  return newChild;
}

//@ requires node(n, _, c);
//@ ensures node(n, _, c) &*& result == c;
int internalGetNbOfNodes(struct Node *n)
{
  //@ open node(n, _, c);
  int c = n->count;
  //@ close node(n, _, c);
  return c;
}

//@ requires node(n, _, c);
//@ ensures node(n, _, c) &*& result == c;
int getNbOfNodes(struct Node *n)
{
  int c = internalGetNbOfNodes(n);
  return c;
}

//@ requires true;
//@ ensures false;
int main()
{
  struct Node *mytree = create();
  struct Node *child = addLeft(mytree);

  struct Node *child2 = addLeft(child);

  int c = getNbOfNodes(child2);
  assert(c == 1);
  abort();
}