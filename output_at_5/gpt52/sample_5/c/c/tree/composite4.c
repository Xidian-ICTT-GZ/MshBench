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
predicate node_fields(struct node *n; struct node *l, struct node *r, struct node *p, int c) =
  n->left |-> l &*& n->right |-> r &*& n->parent |-> p &*& n->count |-> c &*& malloc_block_node(n);

predicate subtree(struct node *n) =
  n == 0 ?
    true
  :
    node_fields(n, ?l, ?r, ?p, ?c) &*& subtree(l) &*& subtree(r);
@*/

struct node * create_node(struct node * p)
  //@ requires true;
  //@ ensures node_fields(result, 0, 0, p, 1);
  

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
  //@ ensures subtree(result);
  

{
  struct node *n = create_node(0);
  //@ close subtree(0);
  //@ close subtree(0);
  //@ close subtree(n);
  
  
  return n;
}

int subtree_get_count(struct node *node)
  //@ requires node == 0 ? true : node_fields(node, ?l, ?r, ?p, ?c) &*& subtree(l) &*& subtree(r);
  //@ ensures node == 0 ? true : node_fields(node, l, r, p, c) &*& subtree(l) &*& subtree(r) &*& result == c;
  

{
  int result = 0;
  
  if (node != 0) { 
    //@ open node_fields(node, ?l, ?r, ?p, ?c);
    result = node->count; 
    //@ close node_fields(node, l, r, p, c);
  }
  
  
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
  //@ requires node_fields(node, ?l, ?r, ?p, ?c) &*& subtree(l) &*& subtree(r);
  //@ ensures node_fields(node, result, r, p, ?c2) &*& subtree(result) &*& subtree(r);
  

  

{
  
  struct node *n = create_node(node);
  //@ close subtree(0);
  //@ close subtree(0);
  //@ close subtree(n);
  
  
  
  {
      struct node *nodeLeft = node->left;
      
      node->left = n;
      

      
      fixup_ancestors(n, node, 1);
      
  }
  

  return n;
}

struct node *tree_add_right(struct node *node)
  //@ requires node_fields(node, ?l, ?r, ?p, ?c) &*& subtree(l) &*& subtree(r);
  //@ ensures node_fields(node, l, result, p, ?c2) &*& subtree(l) &*& subtree(result);
    

    

{
    
    struct node *n = create_node(node);
    //@ close subtree(0);
    //@ close subtree(0);
    //@ close subtree(n);
    
    
    
    {
        struct node *nodeRight = node->right;
        
        node->right = n;
        
        
        fixup_ancestors(n, node, 1);
        
    }
    
    return n;
}

struct node *tree_get_parent(struct node *node)
  //@ requires node_fields(node, ?l, ?r, ?p, ?c) &*& subtree(l) &*& subtree(r);
  //@ ensures node_fields(node, l, r, p, c) &*& subtree(l) &*& subtree(r) &*& result == p;
  

  

{
  
  
  struct node *p = node->parent;
  
  
  
  

  
  
  return p;
}

void subtree_dispose(struct node *node)
  //@ requires subtree(node);
  //@ ensures true;
  
  
{
  
  if (node != 0) {
    //@ open subtree(node);
    //@ open node_fields(node, ?l, ?r, ?p, ?c);
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
  //@ open subtree(node);
  node = tree_add_left(node);
  //@ open subtree(node);
  node = tree_add_right(node);
  //@ open subtree(node);
  node = tree_get_parent(node);
  //@ open subtree(node);
  node = tree_add_left(node);
  //@ open subtree(node);
  node = tree_get_parent(node);
  //@ open subtree(node);
  node = tree_get_parent(node);
  //@ close subtree(node);
  tree_dispose(node);
  return 0;
}

int main() 
  //@ requires true;
  //@ ensures true;
    
    
{
    struct node *root = create_tree();
    //@ open subtree(root);
    struct node *left = tree_add_left(root);
    //@ open subtree(left);
    struct node *leftRight = tree_add_right(left);
    //@ open subtree(leftRight);
    struct node *leftRightParent = tree_get_parent(leftRight);
    
    //@ open subtree(left);
    struct node *leftLeft = tree_add_left(left);
    
    //@ open subtree(leftRight);
    struct node *leftRightRight = tree_add_right(leftRight);
    
    //@ close subtree(root);
    tree_dispose(root);
    return 0;
}