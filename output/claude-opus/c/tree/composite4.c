#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>

struct node
{
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
predicate node(struct node *n, struct node *p) =
  n->left |-> _ &*& n->right |-> _ &*& n->parent |-> p &*& n->count |-> _ &*& malloc_block_node(n);

predicate subtree(struct node *n) =
  n == 0 ? true : node(n, _) &*& subtree(n->left) &*& subtree(n->right);
@*/

struct node *create_node(struct node *p)
//@ requires true;
//@ ensures node(result, p);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0)
  {
    abort();
  }
  n->left = 0;
  n->right = 0;
  n->parent = p;
  n->count = 1;
  //@ close node(n, p);
  return n;
}

struct node *create_tree()
//@ requires true;
//@ ensures node(result, 0);
{
  struct node *n = create_node(0);

  return n;
}

int subtree_get_count(struct node *node)
//@ requires node == 0 ? true : node->count |-> _;
//@ ensures node == 0 ? true : node->count |-> _;
{
  int result = 0;

  if (node != 0)
  {
    result = node->count;
  }

  return result;
}

void fixup_ancestors(struct node *n, struct node *p, int count)
//@ requires p == 0 ? true : p->left |-> _ &*& p->right |-> _ &*& p->parent |-> _ &*& p->count |-> _;
//@ ensures p == 0 ? true : p->left |-> _ &*& p->right |-> _ &*& p->parent |-> _ &*& p->count |-> _;
{

  if (p == 0)
  {
  }
  else
  {
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left)
    {

      leftCount = count;
      rightCount = subtree_get_count(right);
    }
    else
    {
      leftCount = subtree_get_count(left);
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount)
    {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      fixup_ancestors(p, grandparent, pcount);
    }
  }
}

struct node *tree_add_left(struct node *node)
//@ requires node->left |-> _ &*& node->right |-> _ &*& node->parent |-> _ &*& node->count |-> _;
//@ ensures node->left |-> _ &*& node->right |-> _ &*& node->parent |-> _ &*& node->count |-> _ &*& node(result, node);
{

  struct node *n = create_node(node);

  {
    struct node *nodeLeft = node->left;

    node->left = n;

    fixup_ancestors(n, node, 1);
  }

  return n;
}

struct node *tree_add_right(struct node *node)
//@ requires node->left |-> _ &*& node->right |-> _ &*& node->parent |-> _ &*& node->count |-> _;
//@ ensures node->left |-> _ &*& node->right |-> _ &*& node->parent |-> _ &*& node->count |-> _ &*& node(result, node);
{

  struct node *n = create_node(node);

  {
    struct node *nodeRight = node->right;

    node->right = n;

    fixup_ancestors(n, node, 1);
  }

  return n;
}

struct node *tree_get_parent(struct node *node)
//@ requires node->parent |-> ?p;
//@ ensures node->parent |-> p &*& result == p;
{

  struct node *p = node->parent;

  return p;
}

void subtree_dispose(struct node *node)
//@ requires subtree(node);
//@ ensures true;
{

  if (node != 0)
  {
    //@ open subtree(node);
    //@ open node(node, _);
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
  else
  {
    //@ open subtree(node);
  }
}

void tree_dispose(struct node *node)
//@ requires subtree(node);
//@ ensures true;
{

  subtree_dispose(node);
}

int main0()
//@ requires true;
//@ ensures true;
{
  struct node *node = create_tree();
  //@ close subtree(0);
  //@ close subtree(0);
  //@ close subtree(node);
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
  //@ close subtree(0);
  //@ close subtree(0);
  //@ close subtree(root);
  struct node *left = tree_add_left(root);
  struct node *leftRight = tree_add_right(left);
  struct node *leftRightParent = tree_get_parent(leftRight);

  struct node *leftLeft = tree_add_left(left);

  struct node *leftRightRight = tree_add_right(leftRight);

  tree_dispose(root);
  return 0;
}