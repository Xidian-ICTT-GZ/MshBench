//@ #include "stdlib.vf"
//@ #include "limits.vf"

/*@
predicate node(struct Node* n; struct Node* parent, struct Node* left, struct Node* right, int count) =
  n != 0 &*&
  malloc_block_Node(n) &*&
  n->parent |-> parent &*&
  n->left |-> left &*&
  n->right |-> right &*&
  n->count |-> count;
@*/

/*@ predicate nodes(struct Node* n;) = true; @*/

int main() 
  
  
{
  //@ close nodes(0);
  struct Node* mytree = create();
  //@ open nodes(mytree);
  struct Node* child = addLeft(mytree);
  
  struct Node* child2 = addLeft(child);
  
  int c = getNbOfNodes(child2);
  //@ assert c == 1;
  abort();
}

struct Node* create() 
//@ requires true;
//@ ensures node(result, 0, 0, 0, 1);
  
  
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
//@ requires node(node, ?parent, ?old_left, ?right, ?count) &*& old_left == 0;
//@ ensures node(node, parent, result, right, ?new_count) &*& node(result, node, 0, 0, 1);
  
  
{
  
  
  
  
  
  
  
  
  

  
  

  struct Node* newChild = internalAddLeft(node);
  
  
  
  
  
  
  
  return newChild;
}

int getNbOfNodes(struct Node* n)
//@ requires node(n, ?parent, ?left, ?right, ?count);
//@ ensures node(n, parent, left, right, count) &*& result == count;
  
  
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
//@ ensures node(result, parent, 0, 0, 1);
  
  
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  //@ close node(n, parent, 0, 0, 1);
  
  return n;
}

struct Node* internalAddLeft(struct Node* node)
//@ requires node(node, ?parent, 0, ?right, ?count);
//@ ensures node(node, parent, result, right, ?new_count) &*& node(result, node, 0, 0, 1);
  

  

{
    struct Node* child = internalCreate(node);
    //@ open node(node, parent, _, right, count);
    node->left = child;
    //@ close node(node, parent, child, right, count);
    fix(node);
    return child;
}

void fix(struct Node* node)
//@ requires node(node, ?parent, ?left, ?right, ?count) &*& count < INT_MAX;
//@ ensures node(node, parent, left, right, count + 1);
     
  
{
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  //@ open node(node, parent, left, right, count);
  node->count = tmp + 1;
  //@ close node(node, parent, left, right, count + 1);
  
  struct Node* parent = node->parent;
  if(parent==0){
  } else {
    //@ open node(node, parent, left, right, _);
    //@ assert node(parent, ?grandparent, ?pleft, ?pright, ?pcount) &*& pleft == node || pright == node;
    //@ close node(node, parent, left, right, tmp + 1);
    fix(parent);
    //@ open node(node, parent, left, right, tmp + 1);
  }
  
}

void abort()
//@ requires true;
//@ ensures false;
  
  
{
  while(true)
   
  {
  }
}

int internalGetNbOfNodes(struct Node* n)
//@ requires node(n, ?parent, ?left, ?right, ?count);
//@ ensures node(n, parent, left, right, count) &*& result == count;
  
  
{
  
  int c = n->count;
  
  return c;
}