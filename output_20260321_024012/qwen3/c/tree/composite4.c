/*@ 
predicate node(struct node *n; struct node *left, struct node *right, struct node *parent, int count) =
  n != 0 &*&
  malloc_block_node(n) &*&
  n->left |-> left &*&
  n->right |-> right &*&
  n->parent |-> parent &*&
  n->count |-> count;
@*/

#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

struct node * create_node(struct node * p)
//@ requires true;
//@ ensures node(result, 0, 0, p, 1);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  //@ close node(n, 0, 0, p, 1);
  n->left = 0; 
  n->right = 0; 
  n->parent = p;
  n->count = 1;
  
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
//@ requires node(node, ?l, ?r, ?p, ?c) &*& true == (node != 0 ? true : true);
//@ ensures node(node, l, r, p, c) &*& result == (node != 0 ? c : 0);
{
  int result = 0;
  
  if (node != 0) { 
    //@ open node(node, l, r, p, c);
    result = node->count;
    //@ close node(node, l, r, p, c);
  }
  
  
  return result;
}

void fixup_ancestors(struct node * n, struct node * p, int count)
//@ requires 
//@   node(n, ?nl, ?nr, p, ?nc) &*&
//@   (p != 0 ? node(p, ?pl, ?pr, ?pp, ?pc) : true) &*&
//@   (p != 0 ? (n == pl || n == pr) : true) &*&
//@   count >= 0;
//@ ensures 
//@   node(n, nl, nr, p, nc) &*&
//@   (p != 0 ? node(p, pl, pr, pp, _) : true);
{
  
  if (p == 0) {
  } else {
    //@ open node(p, pl, pr, pp, pc);
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
      //@ close node(p, pl, pr, pp, pcount);
      fixup_ancestors(p, grandparent, pcount);
    }
  }
  
}

struct node *tree_add_left(struct node *node)
//@ requires node(node, ?oldLeft, ?r, ?par, ?c);
//@ ensures 
//@   node(node, result, r, par, _) &*&
//@   node(result, 0, 0, node, 1);
{
  
  struct node *n = create_node(node);
  
  
  
  {
      struct node *nodeLeft = node->left;
      //@ open node(node, oldLeft, r, par, c);
      node->left = n;
      //@ close node(node, n, r, par, _);
      
      fixup_ancestors(n, node, 1);
      
  }
  

  return n;
}

struct node *tree_add_right(struct node *node)
//@ requires node(node, ?l, ?oldRight, ?par, ?c);
//@ ensures 
//@   node(node, l, result, par, _) &*&
//@   node(result, 0, 0, node, 1);
{
    
    struct node *n = create_node(node);
    
    
    
    {
        struct node *nodeRight = node->right;
        //@ open node(node, l, oldRight, par, c);
        node->right = n;
        //@ close node(node, l, n, par, _);
        
        
        fixup_ancestors(n, node, 1);
        
    }
    
    return n;
}

struct node *tree_get_parent(struct node *node)
//@ requires node(node, ?l, ?r, ?p, ?c);
//@ ensures node(node, l, r, p, c) &*& result == p;
{
  
  
  struct node *p = node->parent;
  
  
  
  

  
  
  return p;
}

void subtree_dispose(struct node *node)
//@ requires node(node, ?l, ?r, ?p, ?c) &*& true == (node != 0 ? true : true);
//@ ensures true;
{
  
  if (node != 0) {
    //@ open node(node, l, r, p, c);
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