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
  n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count &*& malloc_block_node(n);
@*/

/*@
predicate tree(struct node *n) =
  n == 0 ?
    true
  :
    node(n, ?left, ?right, ?parent, ?count) &*& tree(left) &*& tree(right);
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
//@ ensures tree(result);
{
  struct node *n = create_node(0);
  //@ close tree(0);
  //@ close tree(0);
  //@ close tree(n);
  return n;
}

int subtree_get_count(struct node *node)
//@ requires tree(node);
//@ ensures tree(node);
{
  int result = 0;
  //@ open tree(node);
  if (node != 0) { 
    //@ open node(node, ?left, ?right, ?parent, ?count);
    result = node->count;
    //@ close node(node, left, right, parent, count);
    //@ close tree(node);
  } else {
    //@ close tree(node);
  }
  return result;
}

void fixup_ancestors(struct node * n, struct node * p, int count)
//@ requires p == 0 ? true : node(p, ?left, ?right, ?grandparent, _) &*& (n == left || n == right) &*& tree(n) &*& 0 <= count;
//@ ensures p == 0 ? true : node(p, left, right, grandparent, _) &*& tree(n);
{
  //@ open tree(n);
  if (p == 0) {
    //@ close tree(n);
  } else {
    //@ open node(p, left, right, grandparent, _);
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
      leftCount = count;
      //@ close tree(n);
      rightCount = subtree_get_count(right);
    } else {
      leftCount = subtree_get_count(left);
      rightCount = count;
      //@ close tree(n);
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      //@ close node(p, left, right, grandparent, pcount);
      //@ close tree(p);
      fixup_ancestors(p, grandparent, pcount);
    }
  }
}

struct node *tree_add_left(struct node *node)
//@ requires tree(node);
//@ ensures tree(result) &*& tree(node);
{
  //@ open tree(node);
  //@ open node(node, ?left0, ?right0, ?parent0, ?count0);
  struct node *n = create_node(node);
  //@ close tree(0);
  //@ close tree(0);
  //@ close tree(n);
  {
      struct node *nodeLeft = node->left;
      node->left = n;
      //@ close node(node, n, right0, parent0, count0);
      //@ close tree(node);
      fixup_ancestors(n, node, 1);
  }
  return n;
}

struct node *tree_add_right(struct node *node)
//@ requires tree(node);
//@ ensures tree(result) &*& tree(node);
{
    //@ open tree(node);
    //@ open node(node, ?left0, ?right0, ?parent0, ?count0);
    struct node *n = create_node(node);
    //@ close tree(0);
    //@ close tree(0);
    //@ close tree(n);
    {
        struct node *nodeRight = node->right;
        node->right = n;
        //@ close node(node, left0, n, parent0, count0);
        //@ close tree(node);
        fixup_ancestors(n, node, 1);
    }
    return n;
}

struct node *tree_get_parent(struct node *node)
//@ requires tree(node);
//@ ensures tree(node) &*& tree(result);
{
  //@ open tree(node);
  //@ open node(node, ?left, ?right, ?parent, ?count);
  struct node *p = node->parent;
  //@ close node(node, left, right, parent, count);
  //@ close tree(node);
  //@ if (p != 0) { open tree(p); close tree(p); } else { close tree(0); }
  return p;
}

void subtree_dispose(struct node *node)
//@ requires tree(node);
//@ ensures true;
{
  //@ open tree(node);
  if (node != 0) {
    //@ open node(node, ?left, ?right, ?parent, ?count);
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

void tree_dispose(struct node *node)
//@ requires tree(node);
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