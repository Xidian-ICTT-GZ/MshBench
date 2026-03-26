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
predicate subtree(struct node *node, struct node *parent;) =
    node == 0 ?
        true
    :
        node->left |-> ?left &*&
        node->right |-> ?right &*&
        node->parent |-> parent &*&
        node->count |-> ?count &*&
        malloc_block_node(node) &*&
        subtree(left, node) &*&
        subtree(right, node);

predicate context(struct node *node, struct node *root;) =
    node == root ?
        true
    :
        node->left |-> ?left &*&
        node->right |-> ?right &*&
        node->parent |-> ?parent &*&
        node->count |-> ?count &*&
        malloc_block_node(node) &*&
        parent != 0 &*&
        (parent->left == node ?
            subtree(right, node) &*&
            parent->right |-> ?pright &*&
            subtree(pright, parent)
        :
            subtree(left, node) &*&
            parent->left |-> ?pleft &*&
            subtree(pleft, parent)
        ) &*&
        parent->parent |-> ?gp &*&
        parent->count |-> ?pcount &*&
        malloc_block_node(parent) &*&
        context(parent, root);

predicate tree(struct node *node, struct node *root;) =
    subtree(node, ?p) &*& context(node, root);
@*/

struct node * create_node(struct node * p)
  //@ requires true;
  //@ ensures result != 0 &*& result->left |-> 0 &*& result->right |-> 0 &*& result->parent |-> p &*& result->count |-> 1 &*& malloc_block_node(result);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0; 
  n->right = 0; 
  n->parent = p;
  n->count = 1;
  
  return n;
}

struct node *create_tree()
  //@ requires true;
  //@ ensures subtree(result, 0);
{
  struct node *n = create_node(0);
  //@ close subtree(0, n);
  //@ close subtree(0, n);
  //@ close subtree(n, 0);
  return n;
}

int subtree_get_count(struct node *node)
  //@ requires subtree(node, ?p);
  //@ ensures subtree(node, p) &*& result >= 0;
{
  int result = 0;
  //@ open subtree(node, p);
  if (node != 0) { result = node->count; }
  //@ close subtree(node, p);
  
  return result;
}

void fixup_ancestors(struct node * n, struct node * p, int count)
  //@ requires context(n, ?root) &*& n != root &*& n->parent |-> p &*& n->count |-> ?nc &*& n->left |-> ?nl &*& n->right |-> ?nr &*& malloc_block_node(n) &*& subtree(nl, n) &*& subtree(nr, n) &*& count >= 0;
  //@ ensures context(n, root) &*& n->parent |-> p &*& n->count |-> nc &*& n->left |-> nl &*& n->right |-> nr &*& malloc_block_node(n) &*& subtree(nl, n) &*& subtree(nr, n);
{
  //@ open context(n, root);
  if (p == 0) {
    //@ close context(n, root);
  } else {
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
      leftCount = count;
      //@ close subtree(n, p);
      rightCount = subtree_get_count(right);
      //@ open subtree(n, p);
    } else {
      //@ close subtree(n, p);
      leftCount = subtree_get_count(left);
      //@ open subtree(n, p);
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      //@ close subtree(n, p);
      if (p == root) {
        //@ close context(p, root);
        //@ close context(n, root);
      } else {
        fixup_ancestors(p, grandparent, pcount);
        //@ close context(n, root);
      }
    }
  }
}

struct node *tree_add_left(struct node *node)
  //@ requires subtree(node, ?p) &*& node != 0;
  //@ ensures subtree(result, node) &*& result != 0;
{
  //@ open subtree(node, p);
  struct node *n = create_node(node);
  {
      struct node *nodeLeft = node->left;
      //@ open subtree(nodeLeft, node);
      //@ assert nodeLeft == 0;
      node->left = n;
      //@ close subtree(0, n);
      //@ close subtree(0, n);
      //@ close subtree(n, node);
  }
  return n;
}

struct node *tree_add_right(struct node *node)
  //@ requires subtree(node, ?p) &*& node != 0;
  //@ ensures subtree(result, node) &*& result != 0;
{
    //@ open subtree(node, p);
    struct node *n = create_node(node);
    {
        struct node *nodeRight = node->right;
        //@ open subtree(nodeRight, node);
        //@ assert nodeRight == 0;
        node->right = n;
        //@ close subtree(0, n);
        //@ close subtree(0, n);
        //@ close subtree(n, node);
    }
    return n;
}

struct node *tree_get_parent(struct node *node)
  //@ requires subtree(node, ?p) &*& node != 0;
  //@ ensures subtree(result, ?gp) &*& result == p;
{
  //@ open subtree(node, p);
  struct node *par = node->parent;
  //@ close subtree(node, p);
  return par;
}

void subtree_dispose(struct node *node)
  //@ requires subtree(node, _);
  //@ ensures true;
{
  //@ open subtree(node, _);
  if (node != 0) {
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
  //@ requires subtree(node, ?p);
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