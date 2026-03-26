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
predicate subtree(struct node *n;) =
  n == 0 ? emp : n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> ?p &*& n->count |-> ?c &*& subtree(l) &*& subtree(r);
@*/

//@ requires true;
//@ ensures result->left |-> 0 &*& result->right |-> 0 &*& result->parent |-> p &*& result->count |-> 1 &*& malloc_block_node(result);
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
//@ ensures result->left |-> 0 &*& result->right |-> 0 &*& result->parent |-> 0 &*& result->count |-> 1 &*& malloc_block_node(result);
struct node *create_tree()

{
  struct node *n = create_node(0);

  return n;
}

//@ requires node == 0 ? emp : node->left |-> ?l &*& node->right |-> ?r &*& node->parent |-> ?p &*& node->count |-> ?c;
//@ ensures node == 0 ? emp : node->left |-> l &*& node->right |-> r &*& node->parent |-> p &*& node->count |-> c;
int subtree_get_count(struct node *node)

{
  int result = 0;

  if (node != 0)
  {
    result = node->count;
  }

  return result;
}

//@ requires p == 0 ? emp : p->left |-> ?l &*& p->right |-> ?r &*& p->parent |-> ?gp &*& p->count |-> ?pc &*& (n == l ? emp : subtree(l)) &*& (n == r ? emp : subtree(r));
//@ ensures p == 0 ? emp : p->left |-> l &*& p->right |-> r &*& p->parent |-> gp &*& p->count |-> _ &*& (n == l ? emp : subtree(l)) &*& (n == r ? emp : subtree(r));
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
      //@ close subtree(left);
      //@ close subtree(right);
      //@ open subtree(left);
      //@ open subtree(right);
      fixup_ancestors(p, grandparent, pcount);
    }
  }
}

//@ requires node->left |-> ?l &*& node->right |-> ?r &*& node->parent |-> ?p &*& node->count |-> ?c &*& subtree(l) &*& subtree(r);
//@ ensures result->left |-> 0 &*& result->right |-> 0 &*& result->parent |-> node &*& result->count |-> 1 &*& malloc_block_node(result) &*& node->left |-> result &*& node->right |-> r &*& node->parent |-> p &*& node->count |-> _ &*& subtree(l) &*& subtree(r);
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

//@ requires node->left |-> ?l &*& node->right |-> ?r &*& node->parent |-> ?p &*& node->count |-> ?c &*& subtree(l) &*& subtree(r);
//@ ensures result->left |-> 0 &*& result->right |-> 0 &*& result->parent |-> node &*& result->count |-> 1 &*& malloc_block_node(result) &*& node->left |-> l &*& node->right |-> result &*& node->parent |-> p &*& node->count |-> _ &*& subtree(l) &*& subtree(r);
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

//@ requires node->left |-> ?l &*& node->right |-> ?r &*& node->parent |-> ?p &*& node->count |-> ?c;
//@ ensures node->left |-> l &*& node->right |-> r &*& node->parent |-> p &*& node->count |-> c &*& result == p;
struct node *tree_get_parent(struct node *node)

{

  struct node *p = node->parent;

  return p;
}

//@ requires subtree(node);
//@ ensures emp;
void subtree_dispose(struct node *node)

{
  //@ open subtree(node);
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

//@ requires subtree(node);
//@ ensures emp;
void tree_dispose(struct node *node)

{

  subtree_dispose(node);
}

//@ requires emp;
//@ ensures emp;
int main0()

{
  struct node *node = create_tree();
  //@ close subtree(0);
  //@ close subtree(0);
  node = tree_add_left(node);
  //@ close subtree(0);
  //@ close subtree(0);
  node = tree_add_right(node);
  node = tree_get_parent(node);
  //@ close subtree(0);
  //@ close subtree(0);
  node = tree_add_left(node);
  node = tree_get_parent(node);
  node = tree_get_parent(node);
  //@ close subtree(0);
  //@ close subtree(0);
  //@ close subtree(0);
  //@ close subtree(0);
  //@ close subtree(0);
  //@ close subtree(0);
  //@ close subtree(node);
  tree_dispose(node);
  return 0;
}

//@ requires emp;
//@ ensures emp;
int main()

{
  struct node *root = create_tree();
  //@ close subtree(0);
  //@ close subtree(0);
  struct node *left = tree_add_left(root);
  //@ close subtree(0);
  //@ close subtree(0);
  struct node *leftRight = tree_add_right(left);
  struct node *leftRightParent = tree_get_parent(leftRight);

  //@ close subtree(0);
  //@ close subtree(0);
  struct node *leftLeft = tree_add_left(left);

  //@ close subtree(0);
  //@ close subtree(0);
  struct node *leftRightRight = tree_add_right(leftRight);

  //@ close subtree(0);
  //@ close subtree(leftRightRight);
  //@ close subtree(leftRight);
  //@ close subtree(0);
  //@ close subtree(leftLeft);
  //@ close subtree(left);
  //@ close subtree(0);
  //@ close subtree(root);
  tree_dispose(root);
  return 0;
}