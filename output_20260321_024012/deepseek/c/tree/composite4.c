#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
predicate node(struct node *n; struct node *left, struct node *right, struct node *parent, int count) =
  n->left |-> left
  &*& n->right |-> right
  &*& n->parent |-> parent
  &*& n->count |-> count
  &*& malloc_block_node(n);
@*/

struct node * create_node(struct node * p)
//@ requires true;
//@ ensures node(result, 0, 0, p, 1);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0; 
  n->right = 0; 
  n->parent = p;
  n->count = 1;
  //@ close node(n, 0, 0, p, 1);
  return n;
}

struct node *create_tree()
//@ requires true;
//@ ensures node(result, 0, 0, 0, 1);
{
  struct node *n = create_node(0);
  return n;
}

int subtree_get_count(struct node *node)
//@ requires node(node, ?left, ?right, ?parent, ?count);
//@ ensures node(node, left, right, parent, count) &*& result == count;
{
  int result = 0;
  if (node != 0) { result = node->count; }
  return result;
}

void fixup_ancestors(struct node * n, struct node * p, int count)
//@ requires node(p, ?left, ?right, ?grandparent, ?oldCount) &*& (n == left || n == right);
//@ ensures node(p, left, right, grandparent, ?newCount);
{
  if (p == 0) {
  } else {
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
      leftCount = count;
      rightCount = subtree_get_count(right);
    } else {
      leftCount = subtree_get_count(left);
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
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
//@ requires node(node, ?left, ?right, ?parent, ?count);
//@ ensures node(node, result, right, parent, ?newCount) &*& node(result, 0, 0, node, 1);
{
  struct node *n = create_node(node);
  {
      struct node *nodeLeft = node->left;
      //@ open node(node, left, right, parent, count);
      node->left = n;
      //@ close node(node, n, right, parent, count);
      fixup_ancestors(n, node, 1);
  }
  return n;
}

struct node *tree_add_right(struct node *node)
//@ requires node(node, ?left, ?right, ?parent, ?count);
//@ ensures node(node, left, result, parent, ?newCount) &*& node(result, 0, 0, node, 1);
{
    struct node *n = create_node(node);
    {
        struct node *nodeRight = node->right;
        //@ open node(node, left, right, parent, count);
        node->right = n;
        //@ close node(node, left, n, parent, count);
        fixup_ancestors(n, node, 1);
    }
    return n;
}

struct node *tree_get_parent(struct node *node)
//@ requires node(node, ?left, ?right, ?parent, ?count);
//@ ensures node(node, left, right, parent, count) &*& result == parent;
{
  struct node *p = node->parent;
  return p;
}

void subtree_dispose(struct node *node)
//@ requires node(node, ?left, ?right, ?parent, ?count);
//@ ensures true;
{
  if (node != 0) {
    {
      struct node *left = node->left;
      //@ open node(node, left, right, parent, count);
      subtree_dispose(left);
    }
    {
      struct node *right = node->right;
      subtree_dispose(right);
    }
    //@ open node(node, _, _, _, _);
    free(node);
  }
}

void tree_dispose(struct node *node)
//@ requires node(node, ?left, ?right, ?parent, ?count);
//@ ensures true;
{
  subtree_dispose(node);
}

int main0()
//@ requires true;
//@ ensures true;
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

int main() 
//@ requires true;
//@ ensures true;
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