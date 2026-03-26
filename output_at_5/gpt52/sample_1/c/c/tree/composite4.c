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
predicate subtree(struct node *n;) =
  n == 0 ?
    true
  :
    n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> ?p &*& n->count |-> ?c &*& malloc_block_node(n) &*&
    subtree(l) &*& subtree(r);
@*/

struct node * create_node(struct node * p)
  //@ requires true;
  //@ ensures result->left |-> 0 &*& result->right |-> 0 &*& result->parent |-> p &*& result->count |-> 1 &*& malloc_block_node(result);
  

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
  //@ close subtree(n);
  
  return n;
}

int subtree_get_count(struct node *node)
  //@ requires node == 0 ? true : node->count |-> ?c;
  //@ ensures node == 0 ? true : node->count |-> old(?c0);
  

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
  //@ requires node->left |-> ?l &*& node->right |-> ?r &*& node->parent |-> ?p &*& node->count |-> ?c &*& malloc_block_node(node) &*& subtree(l) &*& subtree(r);
  //@ ensures node->left |-> result &*& node->right |-> ?r2 &*& node->parent |-> ?p2 &*& node->count |-> ?c2 &*& malloc_block_node(node) &*& subtree(result) &*& subtree(r2);
  

  

{
  
  struct node *n = create_node(node);
  //@ close subtree(n);
  
  
  
  {
      struct node *nodeLeft = node->left;
      //@ open subtree(nodeLeft);
      
      node->left = n;
      

      
      fixup_ancestors(n, node, 1);
      
  }
  

  return n;
}

struct node *tree_add_right(struct node *node)
  //@ requires node->left |-> ?l &*& node->right |-> ?r &*& node->parent |-> ?p &*& node->count |-> ?c &*& malloc_block_node(node) &*& subtree(l) &*& subtree(r);
  //@ ensures node->left |-> ?l2 &*& node->right |-> result &*& node->parent |-> ?p2 &*& node->count |-> ?c2 &*& malloc_block_node(node) &*& subtree(l2) &*& subtree(result);
    

    

{
    
    struct node *n = create_node(node);
    //@ close subtree(n);
    
    
    
    {
        struct node *nodeRight = node->right;
        //@ open subtree(nodeRight);
        
        node->right = n;
        
        
        fixup_ancestors(n, node, 1);
        
    }
    
    return n;
}

struct node *tree_get_parent(struct node *node)
  //@ requires node->left |-> ?l &*& node->right |-> ?r &*& node->parent |-> ?p &*& node->count |-> ?c &*& malloc_block_node(node) &*& subtree(l) &*& subtree(r);
  //@ ensures node->left |-> l &*& node->right |-> r &*& node->parent |-> p &*& node->count |-> c &*& malloc_block_node(node) &*& subtree(l) &*& subtree(r) &*& result == p;
  

  

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
  //@ assert node->left |-> ?l &*& node->right |-> ?r &*& node->parent |-> ?p &*& node->count |-> ?c &*& malloc_block_node(node) &*& subtree(l) &*& subtree(r);
  node = tree_add_left(node);
  //@ open subtree(node);
  //@ assert node->left |-> ?l1 &*& node->right |-> ?r1 &*& node->parent |-> ?p1 &*& node->count |-> ?c1 &*& malloc_block_node(node) &*& subtree(l1) &*& subtree(r1);
  node = tree_add_right(node);
  node = tree_get_parent(node);
  node = tree_add_left(node);
  node = tree_get_parent(node);
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
    //@ assert root->left |-> ?l &*& root->right |-> ?r &*& root->parent |-> ?p &*& root->count |-> ?c &*& malloc_block_node(root) &*& subtree(l) &*& subtree(r);
    struct node *left = tree_add_left(root);
    //@ open subtree(left);
    //@ assert left->left |-> ?ll &*& left->right |-> ?lr &*& left->parent |-> ?lp &*& left->count |-> ?lc &*& malloc_block_node(left) &*& subtree(ll) &*& subtree(lr);
    struct node *leftRight = tree_add_right(left);
    struct node *leftRightParent = tree_get_parent(leftRight);
    
    struct node *leftLeft = tree_add_left(left);
    
    struct node *leftRightRight = tree_add_right(leftRight);
    
    
    //@ close subtree(root);
    tree_dispose(root);
    return 0;
}