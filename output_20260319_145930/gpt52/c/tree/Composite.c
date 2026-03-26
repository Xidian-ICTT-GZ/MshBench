#include <stdlib.h>
#include <limits.h>
#include <stdbool.h>

/*@

predicate node(struct Node *n; struct Node *left, struct Node *right, struct Node *parent, int count) =
    n != 0 &*& n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count;

@*/

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

struct Node* create();
//@ requires true;
//@ ensures node(result, ?l, ?r, 0, 1);

struct Node* addLeft(struct Node* node);
//@ requires node(node, ?l, ?r, ?p, ?c);
//@ ensures node(node, result, ?r2, p, ?c2) &*& node(result, 0, 0, node, 1);

int getNbOfNodes(struct Node* n);
//@ requires node(n, ?l, ?r, ?p, ?c);
//@ ensures node(n, l, r, p, c) &*& result == c;

struct Node* internalCreate(struct Node* parent);
//@ requires true;
//@ ensures node(result, 0, 0, parent, 1);

struct Node* internalAddLeft(struct Node* node);
//@ requires node(node, ?l, ?r, ?p, ?c);
//@ ensures node(node, result, ?r2, p, ?c2) &*& node(result, 0, 0, node, 1);

void fix(struct Node* node);
//@ requires node(node, ?l, ?r, ?p, ?c) &*& (p == 0 ? true : node(p, ?pl, ?pr, ?pp, ?pc));
//@ ensures node(node, l, r, p, ?c2) &*& (p == 0 ? true : node(p, pl, pr, pp, ?pc2));

void abort();
//@ requires true;
//@ ensures false;

int internalGetNbOfNodes(struct Node* n);
//@ requires node(n, ?l, ?r, ?p, ?c);
//@ ensures node(n, l, r, p, c) &*& result == c;

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
//@ ensures node(result, ?l, ?r, 0, 1);
  
  
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
  
  //@ close node(n, 0, 0, 0, 1);
  
  return n;
}

struct Node* addLeft(struct Node* node)
//@ requires node(node, ?l, ?r, ?p, ?c);
//@ ensures node(node, result, ?r2, p, ?c2) &*& node(result, 0, 0, node, 1);
  
  
{
  

  struct Node* newChild = internalAddLeft(node);
  
  
  
  
  
  
  
  return newChild;
}

int getNbOfNodes(struct Node* n)
//@ requires node(n, ?l, ?r, ?p, ?c);
//@ ensures node(n, l, r, p, c) &*& result == c;
  
  
{
    int c = internalGetNbOfNodes(n);
    return c;
}

struct Node* internalCreate(struct Node* parent)
//@ requires true;
//@ ensures node(result, 0, 0, parent, 1);
  
  
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  
  //@ close node(n, 0, 0, parent, 1);
  return n;
}

struct Node* internalAddLeft(struct Node* node)
//@ requires node(node, ?l, ?r, ?p, ?c);
//@ ensures node(node, result, ?r2, p, ?c2) &*& node(result, 0, 0, node, 1);
  

  

{
    struct Node* child = internalCreate(node);
    //@ open node(node, l, r, p, c);
    node->left = child;
    //@ close node(node, child, r, p, c);
    fix(node);
    return child;
}

void fix(struct Node* node)
//@ requires node(node, ?l, ?r, ?p, ?c) &*& (p == 0 ? true : node(p, ?pl, ?pr, ?pp, ?pc));
//@ ensures node(node, l, r, p, ?c2) &*& (p == 0 ? true : node(p, pl, pr, pp, ?pc2));
     
  
{
  //@ open node(node, l, r, p, c);
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  
  struct Node* parent = node->parent;
  if(parent==0){
    //@ close node(node, l, r, p, tmp + 1);
  } else {
    //@ close node(node, l, r, p, tmp + 1);
    //@ open node(parent, pl, pr, pp, pc);
    //@ close node(parent, pl, pr, pp, pc);
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
//@ requires node(n, ?l, ?r, ?p, ?c);
//@ ensures node(n, l, r, p, c) &*& result == c;
  
  
{
  //@ open node(n, l, r, p, c);
  int c = n->count;
  //@ close node(n, l, r, p, c);
  return c;
}