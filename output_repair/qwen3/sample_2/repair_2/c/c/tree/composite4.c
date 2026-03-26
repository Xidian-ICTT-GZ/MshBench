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

/*@ predicate node(struct node *n; struct node *l, struct node *r, struct node *p, int c) =
  n != 0 &*& n->left |-> l &*& n->right |-> r &*& n->parent |-> p &*& n->count |-> c;
@*/

/*@ predicate tree(struct node *n) =
  n == 0 || (node(n, ?l, ?r, ?p, ?c) &*& tree(l) &*& tree(r));
@*/

/*@ predicate valid_count(struct node *n) =
  n == 0 ||
  (node(n, ?l, ?r, ?p, ?c) &*& valid_count(l) &*& valid_count(r) &*& c == 1 + subtree_get_count(l) + subtree_get_count(r));
@*/

//@ requires true;
//@ ensures node(result, 0, 0, p, 1);
struct node *create_node(struct node *p)
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

  return n;
}

//@ requires true;
//@ ensures tree(result) &*& node(result, 0, 0, 0, 1);
struct node *create_tree()
{
  struct node *n = create_node(0);

  return n;
}

//@ requires tree(node);
//@ ensures result == (node == 0 ? 0 : node->count);
int subtree_get_count(struct node *node)
{
  int result = 0;

  if (node != 0)
  {
    result = node->count;
  }

  return result;
}

//@ requires node(p, ?l, ?r, ?gp, _) &*& tree(l) &*& tree(r) &*& n != 0 &*& (n == l || n == r);
//@ ensures tree(p) &*& node(p, ?l2, ?r2, gp, ?pc) &*& pc == 1 + subtree_get_count(l2) + subtree_get_count(r2);
void fixup_ancestors(struct node *n, struct node *p, int count)
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

//@ requires node(node, ?l, ?r, ?p, ?c) &*& tree(l) &*& tree(r);
//@ ensures node(result, 0, 0, node, 1) &*& node(node, result, ?r2, ?p2, ?c2) &*& tree(r2) &*& c2 == 1 + 1 + subtree_get_count(r2);
struct node *tree_add_left(struct node *node)
{
  struct node *n = create_node(node);

  {
    struct node *nodeLeft = node->left;

    node->left = n;

    fixup_ancestors(n, node, 1);
  }

  return n;
}

//@ requires node(node, ?l, ?r, ?p, ?c) &*& tree(l) &*& tree(r);
//@ ensures node(result, 0, 0, node, 1) &*& node(node, ?l2, result, ?p2, ?c2) &*& tree(l2) &*& c2 == 1 + subtree_get_count(l2) + 1;
struct node *tree_add_right(struct node *node)
{
  struct node *n = create_node(node);

  {
    struct node *nodeRight = node->right;

    node->right = n;

    fixup_ancestors(n, node, 1);
  }

  return n;
}

//@ requires node(node, ?l, ?r, ?p, ?c) &*& tree(l) &*& tree(r);
//@ ensures result == p;
struct node *tree_get_parent(struct node *node)
{
  struct node *p = node->parent;

  return p;
}

//@ requires tree(node);
//@ ensures true;
void subtree_dispose(struct node *node)
{
  if (node != 0)
  {
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

//@ requires tree(node);
//@ ensures true;
void tree_dispose(struct node *node)
{
  subtree_dispose(node);
}

//@ requires true;
//@ ensures true;
int main0()
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

//@ requires true;
//@ ensures true;
int main()
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