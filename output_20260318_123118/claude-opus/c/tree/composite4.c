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

predicate tree(struct node *n; int cnt) =
  n == 0 ?
    true
  :
    malloc_block_node(n) &*&
    n->parent |-> ?p &*&
    n->count |-> cnt &*&
    n->left |-> ?l &*& n->right |-> ?r &*&
    tree(l; ?lc) &*& tree(r; ?rc) &*&
    cnt == 1 + lc + rc &*&
    ((l == 0 || l->parent == n) && (r == 0 || r->parent == n));
  
predicate malloc_block_node(struct node *p) = malloc_block(p, sizeof(struct node));

@*/

//@ requires true;
//@ ensures  malloc_block_node(result) &*& result->left |-> 0 &*& result->right |-> 0 &*& result->parent |-> p &*& result->count |-> 1 &*& tree(result; 1);
struct node * create_node(struct node * p)
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0; 
  n->right = 0; 
  n->parent = p;
  n->count = 1;
  
  return n;
}

//@ requires true;
//@ ensures tree(result; 1);
struct node *create_tree()
{
  struct node *n = create_node(0);
  
  return n;
}

//@ requires true;
//@ ensures result == 0 || (result == node->count && node != 0);
int subtree_get_count(struct node *node)
{
  int result = 0;
  
  if (node != 0) { result = node->count; }
  
  return result;
}

//@ requires n != 0 &*& p != 0 &*& tree(n; _) &*& tree(p; _) &*& (p->left == n || p->right == n) &*& (p->parent == 0 || tree(p->parent; _));
//@ ensures tree(p; _) &*& (p->parent == 0 || tree(p->parent; _)) &*& tree(n; _);
void fixup_ancestors(struct node * n, struct node * p, int count)
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

//@ requires node != 0 &*& tree(node; ?cnt);
//@ ensures malloc_block_node(result) &*& tree(result; 1) &*& node->left |-> result;
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

//@ requires node != 0 &*& tree(node; ?cnt);
//@ ensures malloc_block_node(result) &*& tree(result; 1) &*& node->right |-> result;
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

//@ requires node != 0 &*& tree(node; _);
//@ ensures result == node->parent;
struct node *tree_get_parent(struct node *node)
{
  struct node *p = node->parent;
  return p;
}

//@ requires tree(node; _);
//@ ensures true;
void subtree_dispose(struct node *node)
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
    free(node);
  }
}

//@ requires tree(node; _);
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