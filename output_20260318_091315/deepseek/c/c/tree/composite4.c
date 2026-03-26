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

/*@
predicate subtree(struct node *n) =
  n == 0 ? true : node(n, ?left, ?right, ?parent, ?count) &*& subtree(left) &*& subtree(right);
@*/

/*@
lemma void subtree_merge(struct node *n)
requires subtree(n);
ensures subtree(n);
{ open subtree(n); if (n != 0) { open node(n, _, _, _, _); } close subtree(n); }
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
//@ ensures subtree(result);
{
  struct node *n = create_node(0);
  //@ close subtree(0);
  //@ close subtree(0);
  //@ close subtree(n);
  return n;
}

int subtree_get_count(struct node *node)
//@ requires subtree(node);
//@ ensures subtree(node);
{
  int result = 0;
  //@ open subtree(node);
  if (node != 0) { 
    //@ open node(node, ?left, ?right, ?parent, ?count);
    result = node->count;
    //@ close node(node, left, right, parent, count);
  }
  //@ close subtree(node);
  return result;
}

void fixup_ancestors(struct node * n, struct node * p, int count)
//@ requires p == 0 ? true : node(p, ?left, ?right, ?grandparent, _) &*& subtree(left) &*& subtree(right) &*& (n == left || n == right);
//@ ensures p == 0 ? true : node(p, left, right, grandparent, _) &*& subtree(left) &*& subtree(right);
{
  if (p == 0) {
  } else {
    //@ open node(p, left, right, grandparent, _);
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
      leftCount = count;
      //@ close subtree(left);
      rightCount = subtree_get_count(right);
    } else {
      leftCount = subtree_get_count(left);
      rightCount = count;
      //@ close subtree(right);
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      //@ close node(p, left, right, grandparent, pcount);
      fixup_ancestors(p, grandparent, pcount);
      //@ open node(p, left, right, grandparent, pcount);
    }
    //@ close node(p, left, right, grandparent, pcount);
  }
}

struct node *tree_add_left(struct node *node)
//@ requires subtree(node) &*& node != 0;
//@ ensures subtree(result) &*& subtree(node);
{
  struct node *n = create_node(node);
  //@ open subtree(node);
  //@ open node(node, ?oldLeft, ?oldRight, ?parent, ?count);
  {
      struct node *nodeLeft = node->left;
      node->left = n;
      //@ close subtree(0);
      //@ close subtree(0);
      //@ close subtree(n);
      //@ close subtree(oldRight);
      fixup_ancestors(n, node, 1);
      //@ open subtree(n);
      //@ open subtree(oldRight);
  }
  //@ close subtree(node);
  return n;
}

struct node *tree_add_right(struct node *node)
//@ requires subtree(node) &*& node != 0;
//@ ensures subtree(result) &*& subtree(node);
{
    struct node *n = create_node(node);
    //@ open subtree(node);
    //@ open node(node, ?oldLeft, ?oldRight, ?parent, ?count);
    {
        struct node *nodeRight = node->right;
        node->right = n;
        //@ close subtree(0);
        //@ close subtree(0);
        //@ close subtree(n);
        //@ close subtree(oldLeft);
        fixup_ancestors(n, node, 1);
        //@ open subtree(n);
        //@ open subtree(oldLeft);
    }
    //@ close subtree(node);
    return n;
}

struct node *tree_get_parent(struct node *node)
//@ requires subtree(node) &*& node != 0;
//@ ensures subtree(result) &*& subtree(node);
{
  //@ open subtree(node);
  //@ open node(node, ?left, ?right, ?parent, ?count);
  struct node *p = node->parent;
  //@ close node(node, left, right, parent, count);
  //@ close subtree(node);
  //@ subtree_merge(p);
  return p;
}

void subtree_dispose(struct node *node)
//@ requires subtree(node);
//@ ensures true;
{
  if (node != 0) {
    //@ open subtree(node);
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