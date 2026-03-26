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
predicate tree(struct node *n) =
  n == 0 ?
    true
  :
    n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> ?p &*& n->count |-> ?c &*& malloc_block_node(n) &*& tree(l) &*& tree(r);
@*/

struct node * create_node(struct node * p)
  //@ requires true;
  //@ ensures tree(result);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0; 
  n->right = 0; 
  n->parent = p;
  n->count = 1;
  //@ close tree(0);
  //@ close tree(0);
  //@ close tree(n);
  return n;
}

struct node *create_tree()
  //@ requires true;
  //@ ensures tree(result);
{
  struct node *n = create_node(0);
  return n;
}

int subtree_get_count(struct node *node)
  //@ requires node == 0 ? true : node->count |-> ?c;
  //@ ensures node == 0 ? true : node->count |-> ?c;
{
  int result = 0;
  
  if (node != 0) { result = node->count; }
  
  
  return result;
}

void fixup_ancestors(struct node * n, struct node * p, int count)
  //@ requires true;
  //@ ensures true;
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
  //@ requires tree(node);
  //@ ensures tree(node) &*& tree(result);
{
  
  //@ open tree(node);
  struct node *n = create_node(node);
  
  
  
  {
      struct node *nodeLeft = node->left;
      //@ open tree(nodeLeft);
      node->left = n;
      

      
      fixup_ancestors(n, node, 1);
      
      //@ close tree(nodeLeft);
  }
  
  //@ close tree(node);
  return n;
}

struct node *tree_add_right(struct node *node)
  //@ requires tree(node);
  //@ ensures tree(node) &*& tree(result);
{
    
    //@ open tree(node);
    struct node *n = create_node(node);
    
    
    
    {
        struct node *nodeRight = node->right;
        //@ open tree(nodeRight);
        node->right = n;
        
        
        fixup_ancestors(n, node, 1);
        
        //@ close tree(nodeRight);
    }
    
    //@ close tree(node);
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
  //@ requires tree(node);
  //@ ensures true;
{
  
  if (node != 0) {
    //@ open tree(node);
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
  //@ open tree(node);
  node = tree_add_left(node);
  //@ open tree(node);
  node = tree_add_right(node);
  struct node *p1 = tree_get_parent(node);
  //@ open tree(p1);
  node = p1;
  node = tree_add_left(node);
  struct node *p2 = tree_get_parent(node);
  //@ open tree(p2);
  node = p2;
  struct node *p3 = tree_get_parent(node);
  node = p3;
  //@ close tree(0);
  //@ close tree(0);
  //@ close tree(node);
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