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
predicate node(struct node *n; struct node *l, struct node *r, struct node *p, int c) =
  n->left |-> l &*& n->right |-> r &*& n->parent |-> p &*& n->count |-> c &*& malloc_block_node(n);
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
  //@ assert node(n, 0, 0, 0, 1);
  return n;
}

int subtree_get_count(struct node *node)
//@ requires node(node, ?l, ?r, ?p, ?c);
//@ ensures node(node, l, r, p, c) &*& result == c;
{
  int result = 0;
  //@ open node(node, l, r, p, c);
  if (node != 0) { result = node->count; }
  //@ close node(node, l, r, p, c);
  return result;
}

void fixup_ancestors(struct node * n, struct node * p, int count)
//@ requires node(p, ?l, ?r, ?gp, ?oldc) &*& (n == l || n == r);
//@ ensures node(p, l, r, gp, ?newc);
{
  //@ open node(p, l, r, gp, oldc);
  if (p == 0) {
    //@ close node(p, l, r, gp, oldc);
  } else {
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
      leftCount = count;
      //@ open node(p, l, r, gp, oldc);
      //@ close node(p, l, r, gp, oldc);
      rightCount = subtree_get_count(right);
    } else {
      //@ open node(p, l, r, gp, oldc);
      //@ close node(p, l, r, gp, oldc);
      leftCount = subtree_get_count(left);
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      //@ close node(p, l, r, gp, pcount);
      fixup_ancestors(p, grandparent, pcount);
      //@ open node(p, l, r, gp, ?newc);
    }
  }
  //@ close node(p, l, r, gp, _);
}

struct node *tree_add_left(struct node *node)
//@ requires node(node, ?l, ?r, ?p, ?c) &*& l == 0;
//@ ensures node(node, result, r, p, ?c2) &*& node(result, 0, 0, node, 1);
{
  //@ open node(node, l, r, p, c);
  struct node *n = create_node(node);
  //@ close node(n, 0, 0, node, 1);
  {
      struct node *nodeLeft = node->left;
      node->left = n;
      //@ close node(node, n, r, p, c);
      fixup_ancestors(n, node, 1);
      //@ open node(node, n, r, p, ?c2);
  }
  //@ close node(node, n, r, p, c2);
  return n;
}

struct node *tree_add_right(struct node *node)
//@ requires node(node, ?l, ?r, ?p, ?c) &*& r == 0;
//@ ensures node(node, l, result, p, ?c2) &*& node(result, 0, 0, node, 1);
{
    //@ open node(node, l, r, p, c);
    struct node *n = create_node(node);
    //@ close node(node, l, n, p, c);
    {
        struct node *nodeRight = node->right;
        node->right = n;
        //@ close node(node, l, n, p, c);
        fixup_ancestors(n, node, 1);
        //@ open node(node, l, n, p, ?c2);
    }
    //@ close node(node, l, n, p, c2);
    return n;
}

struct node *tree_get_parent(struct node *node)
//@ requires node(node, ?l, ?r, ?p, ?c);
//@ ensures node(node, l, r, p, c) &*& result == p;
{
  //@ open node(node, l, r, p, c);
  struct node *p = node->parent;
  //@ close node(node, l, r, p, c);
  return p;
}

void subtree_dispose(struct node *node)
//@ requires node(node, ?l, ?r, ?p, ?c);
//@ ensures true;
{
  //@ open node(node, l, r, p, c);
  if (node != 0) {
    {
      struct node *left = node->left;
      //@ open node(node, l, r, p, c);
      //@ close node(node, l, r, p, c);
      subtree_dispose(left);
    }
    {
      struct node *right = node->right;
      //@ open node(node, l, r, p, c);
      //@ close node(node, l, r, p, c);
      subtree_dispose(right);
    }
    free(node);
  }
}

void tree_dispose(struct node *node)
//@ requires node(node, ?l, ?r, ?p, ?c);
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