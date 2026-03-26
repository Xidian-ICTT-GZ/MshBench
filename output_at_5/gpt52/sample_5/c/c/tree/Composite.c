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
  n != 0 &*& malloc_block_Node(n) &*&
  n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count;

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
  //@ ensures Node(result, 0, 0, 0, 1);
  
  
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
  return n;
}

struct Node* addLeft(struct Node* node)
  //@ requires Node(node, ?l, ?r, ?p, ?c);
  //@ ensures Node(node, ?l2, r, p, ?c2) &*& Node(result, 0, 0, node, 1);
  
  
{
  
  
  
  
  
  
  
  
  

  
  

  struct Node* newChild = internalAddLeft(node);
  
  
  
  
  
  
  
  return newChild;
}

int getNbOfNodes(struct Node* n)
  //@ requires Node(n, ?l, ?r, ?p, ?cnt);
  //@ ensures Node(n, l, r, p, cnt) &*& result == cnt;
  
  
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
  //@ ensures Node(node, ?l2, r, p, ?c2) &*& Node(result, 0, 0, node, 1);
  

  

{
    //@ open Node(node, l, r, p, c);
    struct Node* child = internalCreate(node);
    node->left = child;
    //@ close Node(node, child, r, p, c);
    fix(node);
    return child;
}

void fix(struct Node* node)
  //@ requires Node(node, ?l, ?r, ?p, ?c);
  //@ ensures Node(node, l, r, p, ?c2);
     
  
{
  //@ open Node(node, l, r, p, c);
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  
  struct Node* parent = node->parent;
  //@ close Node(node, l, r, p, tmp + 1);
  if(parent==0){
  } else {
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
  //@ ensures Node(n, l, r, p, c) &*& result == c;
  
  
{
  
  //@ open Node(n, l, r, p, c);
  int c = n->count;
  //@ close Node(n, l, r, p, c);
  
  return c;
}