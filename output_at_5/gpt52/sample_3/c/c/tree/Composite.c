#include <stdlib.h>
#include <limits.h>
#include <stdbool.h>

struct Node;
struct Node* create();
struct Node* addLeft(struct Node* node);
int getNbOfNodes(struct Node* n);
struct Node* internalCreate(struct Node* parent);
struct Node* internalAddLeft(struct Node* node);
void fix(struct Node* node);
void abort();
int internalGetNbOfNodes(struct Node* n);

/*@

predicate Node(struct Node* n; struct Node* left, struct Node* right, struct Node* parent, int count) =
  n != 0 &*& malloc_block(n, sizeof(struct Node)) &*&
  n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count;

predicate tree(struct Node* n) =
  n == 0 ?
    true
  :
    Node(n, ?l, ?r, ?p, ?c) &*& tree(l) &*& tree(r);

@*/

int main() 
  //@ requires true;
  //@ ensures true;
  
  
{
  struct Node* mytree = create();
  struct Node* child = addLeft(mytree);
  
  struct Node* child2 = addLeft(child);
  
  int c = getNbOfNodes(child2);
  assert(c==1);
  abort();
}

struct Node* create() 
  //@ requires true;
  //@ ensures tree(result);
  
  
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0){
    abort();
  } else {
  }
  n->parent = 0;
  n->left = 0;
  n->right = 0;
  n->count = 1;
  
  
  
  //@ close Node(n, 0, 0, 0, 1);
  //@ close tree(0);
  //@ close tree(0);
  //@ close tree(n);
  return n;
}

struct Node* addLeft(struct Node* node)
  //@ requires tree(node);
  //@ ensures tree(node);
  
  
{
  
  
  
  
  
  
  
  
  

  
  

  struct Node* newChild = internalAddLeft(node);
  
  
  
  
  
  
  
  return newChild;
}

int getNbOfNodes(struct Node* n)
  //@ requires Node(n, ?l, ?r, ?p, ?c);
  //@ ensures Node(n, l, r, p, c);
  
  
{
    
    
    
    
    
    
    int c = internalGetNbOfNodes(n);
    
    
    
    return c;
}

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

struct Node* internalCreate(struct Node* parent)
  //@ requires true;
  //@ ensures Node(result, 0, 0, parent, 1);
  
  
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  
  //@ close Node(n, 0, 0, parent, 1);
  return n;
}

struct Node* internalAddLeft(struct Node* node)
  //@ requires Node(node, ?l, ?r, ?p, ?c);
  //@ ensures Node(node, ?l2, r, p, ?c2);
  

  

{
    struct Node* child = internalCreate(node);
    //@ open Node(node, l, r, p, c);
    node->left = child;
    //@ close Node(node, child, r, p, c);
    fix(node);
    //@ open Node(child, 0, 0, node, 1);
    //@ close Node(child, 0, 0, node, 1);
    return child;
}

void fix(struct Node* node)
  //@ requires Node(node, ?l, ?r, ?p, ?c);
  //@ ensures Node(node, l, r, p, ?c2);
     
  
{
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  
  struct Node* parent = node->parent;
  if(parent==0){
    //@ open Node(node, l, r, p, c);
    //@ close Node(node, l, r, p, tmp + 1);
  } else {
    //@ open Node(node, l, r, p, c);
    //@ close Node(node, l, r, p, tmp + 1);
    fix(parent);
  }
  
}

void abort()
  //@ requires true;
  //@ ensures false;
  
  
{
  while(true)
   
  //@ invariant true;
  {
  }
}

int internalGetNbOfNodes(struct Node* n)
  //@ requires Node(n, ?l, ?r, ?p, ?c);
  //@ ensures Node(n, l, r, p, c);
  
  
{
  
  int c = n->count;
  
  return c;
}