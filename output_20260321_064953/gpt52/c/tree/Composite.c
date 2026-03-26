int malloc_block_Node(struct Node* p);

/*@

predicate node(struct Node* n; struct Node* left, struct Node* right, struct Node* parent, int count) =
  n != 0 &*&
  n->left |-> left &*&
  n->right |-> right &*&
  n->parent |-> parent &*&
  n->count |-> count &*&
  malloc_block_Node(n);

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
  //@ ensures node(result, ?l, ?r, ?p, ?c);
  
  
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
  //@ ensures node(node, result, ?r2, ?p2, ?c2) &*& node(result, ?lch, ?rch, node, ?cch);
  
  
{
  
  
  
  
  
  
  
  
  

  
  

  //@ open node(node, l, r, p, c);
  struct Node* newChild = internalAddLeft(node);
  //@ close node(node, newChild, r, p, c + 1);
  
  
  
  
  
  
  
  return newChild;
}

int getNbOfNodes(struct Node* n)
  //@ requires node(n, ?l, ?r, ?p, ?c);
  //@ ensures node(n, l, r, p, c) &*& result == c;
  
  
{
    
    
    
    
    
    
    //@ open node(n, l, r, p, c);
    int c = internalGetNbOfNodes(n);
    //@ close node(n, l, r, p, c);
    
    
    
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
  //@ ensures node(node, result, ?r2, ?p2, ?c2) &*& node(result, 0, 0, node, 1);
  

  

{
    //@ open node(node, l, r, p, c);
    struct Node* child = internalCreate(node);
    node->left = child;
    //@ close node(node, child, r, p, c);
    fix(node);
    //@ open node(node, child, r, p, c + 1);
    //@ close node(node, child, r, p, c + 1);
    return child;
}

void fix(struct Node* node)
  //@ requires node(node, ?l, ?r, ?p, ?c);
  //@ ensures node(node, l, r, p, c + 1);
     
  
{
  //@ open node(node, l, r, p, c);
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  
  struct Node* parent = node->parent;
  if(parent==0){
    //@ close node(node, l, r, p, c + 1);
  } else {
    //@ close node(node, l, r, p, c + 1);
    fix(parent);
  }
  
}

void abort()
  //@ requires true;
  //@ ensures true;
  
  
{
  while(true)
   
  //@ invariant true;
  {
  }
}

int internalGetNbOfNodes(struct Node* n)
  //@ requires n->count |-> ?c;
  //@ ensures n->count |-> c &*& result == c;
  
  
{
  
  int c = n->count;
  
  return c;
}