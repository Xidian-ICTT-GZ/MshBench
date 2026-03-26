#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@ predicate tree(struct node *n; int count) =
      n == 0 ?
        count == 0
      :
        n->count |-> count &*& n->left |-> ?left &*& n->right |-> ?right &*& n->parent |-> ?parent &
        tree(left, ?leftCount) &*& tree(right, ?rightCount) &*& count == 1 + leftCount + rightCount &*&
        (parent == 0 || parent->left == n || parent->right == n);
@*/

struct node * create_node(struct node * p)
  
  //@ requires true;
  //@ ensures tree(result, 1) &*& result->parent |-> p;
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
  //@ ensures tree(result, 1);
{
  struct node *n = create_node(0);
  
  
  return n;
}

int subtree_get_count(struct node *node)
  
  //@ requires tree(node, ?count);
  //@ ensures tree(node, count) &*& result == count;
{
  int result = 0;
  
  if (node != 0) { result = node->count; }
  
  
  return result;
}

void fixup_ancestors(struct node * n, struct node * p, int count)
  //@ requires tree(n, count) &*& (p == 0 || tree(p, ?pcount));
  //@ ensures (p == 0 ? true : tree(p, 1 + subtree_get_count(p->left) + subtree_get_count(p->right))) &*& tree(n, count);
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
  
  //@ requires tree(node, ?count);
  //@ ensures tree(node, ?newCount) &*& tree(result, 1) &*& node->left == result &*& result->parent == node;
{
  
  struct node *n = create_node(node);
  
  
  
  {
      struct node *nodeLeft = node->left;
      
      node->left = n;
      

      
      fixup_ancestors(n, node, 1);
      
  }
  

  return n;
}

struct node *tree_add_right(struct node *node)
  
  //@ requires tree(node, ?count);
  //@ ensures tree(node, ?newCount) &*& tree(result, 1) &*& node->right == result &*& result->parent == node;
{
    
    struct node *n = create_node(node);
    
    
    
    {
        struct node *nodeRight = node->right;
        
        node->right = n;
        
        
        fixup_ancestors(n, node, 1);
        
    }
    
    return n;
}

struct node *tree_get_parent(struct node *node)
  
  //@ requires tree(node, ?count) &*& node != 0;
  //@ ensures tree(node, count) &*& (result == 0 ? true : tree(result, ?pcount));
{
  
  
  struct node *p = node->parent;
  
  
  
  

  
  
  return p;
}

void subtree_dispose(struct node *node)
  
  //@ requires tree(node, ?count);
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
    free(node);
  }
}

void tree_dispose(struct node *node)
  
  //@ requires tree(node, ?count);
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