#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>

/*@
predicate nodes(struct node *n;) = 
  n == 0 ? true :
    n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> ?p &*& n->count |-> ?c &*& malloc_block_node(n) &*&
    nodes(l) &*& nodes(r);
@*/

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

struct node * create_node(struct node * p)
  //@ requires true;
  //@ ensures nodes(result);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0; 
  n->right = 0; 
  n->parent = p;
  n->count = 1;
  //@ close nodes(n);
  return n;
}

struct node *create_tree()
  //@ requires true;
  //@ ensures nodes(result);
{
  struct node *n = create_node(0);
  //@ close nodes(n);
  return n;
}

int subtree_get_count(struct node *node)
  //@ requires nodes(node);
  //@ ensures nodes(node) &*& result == (node == 0 ? 0 : node->count);
{
  int result = 0;
  if (node != 0) { result = node->count; }
  return result;
}

void fixup_ancestors(struct node * n, struct node * p, int count)
  //@ requires nodes(p);
  //@ ensures nodes(p);
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
  //@ requires nodes(node);
  //@ ensures nodes(node) &*& nodes(result);
{
  struct node *n = create_node(node);
  {
      struct node *nodeLeft = node->left;
      node->left = n;
      fixup_ancestors(n, node, 1);
  }
  //@ close nodes(n);
  return n;
}

struct node *tree_add_right(struct node *node)
  //@ requires nodes(node);
  //@ ensures nodes(node) &*& nodes(result);
{
  struct node *n = create_node(node);
  {
      struct node *nodeRight = node->right;
      node->right = n;
      fixup_ancestors(n, node, 1);
  }
  //@ close nodes(n);
  return n;
}

struct node *tree_get_parent(struct node *node)
  //@ requires nodes(node);
  //@ ensures nodes(node) &*& (result == node->parent);
{
  struct node *p = node->parent;
  return p;
}

void subtree_dispose(struct node *node)
  //@ requires nodes(node);
  //@ ensures true;
{
  if (node != 0) {
    {
      struct node *left = node->left;
      subtree_dispose(left);
    }
    {
      struct node *right = node->right;
      subtree_dispose(right);
    }
    //@ open nodes(node);
    free(node);
  }
}

void tree_dispose(struct node *node)
  //@ requires nodes(node);
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