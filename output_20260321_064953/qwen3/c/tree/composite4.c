#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>

/*@ 
predicate node(struct node *n; struct node *left, struct node *right, struct node *parent, int count) =
  n != 0 &*&
  malloc_block_node(n) &*&
  n->left |-> left &*&
  n->right |-> right &*&
  n->parent |-> parent &*&
  n->count |-> count;
@*/

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

//@ requires true;
//@ ensures node(result, 0, 0, p, 1);
struct node * create_node(struct node * p)
  
  

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

//@ requires true;
//@ ensures node(result, 0, 0, 0, 1);
struct node *create_tree()
  
  

{
  struct node *n = create_node(0);
  
  
  return n;
}

//@ requires node(node, ?l, ?r, ?p, ?c) &*& true;
//@ ensures node(node, l, r, p, c) &*& result == c;
int subtree_get_count(struct node *node)
  
  

{
  int result = 0;
  
  if (node != 0) { 
    //@ open node(node, _, _, _, _);
    result = node->count;
    //@ close node(node, _, _, _, _);
  }
  
  
  return result;
}

//@ requires node(n, _, _, p, _) &*& node(p, ?pl, ?pr, ?gp, ?pc) &*& true;
//@ ensures node(n, _, _, p, _) &*& node(p, pl, pr, gp, _) &*& true;
void fixup_ancestors(struct node * n, struct node * p, int count)
  
  
{
  
  if (p == 0) {
  } else {
    //@ open node(p, _, _, _, _);
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
      //@ close node(p, left, right, grandparent, pcount);
      fixup_ancestors(p, grandparent, pcount);
    }
  }
  
}

//@ requires node(node, ?l, ?r, ?p, ?c) &*& true;
//@ ensures node(result, 0, 0, node, 1) &*& node(node, result, r, p, _) &*& true;
struct node *tree_add_left(struct node *node)
  

  

{
  
  struct node *n = create_node(node);
  
  
  
  {
      struct node *nodeLeft = node->left;
      //@ open node(node, _, _, _, _);
      node->left = n;
      //@ close node(node, n, r, p, _);

      
      fixup_ancestors(n, node, 1);
      
  }
  

  return n;
}

//@ requires node(node, ?l, ?r, ?p, ?c) &*& true;
//@ ensures node(result, 0, 0, node, 1) &*& node(node, l, result, p, _) &*& true;
struct node *tree_add_right(struct node *node)
    

    

{
    
    struct node *n = create_node(node);
    
    
    
    {
        struct node *nodeRight = node->right;
        //@ open node(node, _, _, _, _);
        node->right = n;
        //@ close node(node, l, n, p, _);
        
        
        fixup_ancestors(n, node, 1);
        
    }
    
    return n;
}

//@ requires node(node, ?l, ?r, ?p, ?c) &*& true;
//@ ensures node(node, l, r, p, c) &*& result == p;
struct node *tree_get_parent(struct node *node)
  

  

{
  
  
  struct node *p = node->parent;
  
  
  
  

  
  
  return p;
}

//@ requires node(node, ?l, ?r, ?p, ?c) &*& true;
//@ ensures true;
void subtree_dispose(struct node *node)
  
  
{
  
  if (node != 0) {
    //@ open node(node, ?left, ?right, _, _);
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

//@ requires node(node, ?l, ?r, ?p, ?c) &*& true;
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