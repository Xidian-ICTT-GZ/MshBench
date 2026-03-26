int malloc_block_Node(struct Node* p);

/*@
predicate Node(struct Node* n; struct Node* left, struct Node* right, struct Node* parent, int count) =
  n != 0 &*& malloc_block_Node(n) &*& n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count;

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
  //@ ensures tree(node) &*& tree(result);
  
  
{
  
  
  
  
  
  
  
  
  

  
  

  //@ open tree(node);
  struct Node* newChild = internalAddLeft(node);
  //@ close tree(node);
  
  
  
  
  
  
  
  return newChild;
}

int getNbOfNodes(struct Node* n)
  //@ requires tree(n);
  //@ ensures tree(n) &*& result >= 0;
  
  
{
    
    
    
    
    
    
    //@ open tree(n);
    int c = internalGetNbOfNodes(n);
    //@ close tree(n);
    
    
    
    return c;
}

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

struct Node* internalCreate(struct Node* parent)
  //@ requires tree(parent);
  //@ ensures tree(parent) &*& tree(result);
  
  
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
  //@ close tree(0);
  //@ close tree(0);
  //@ close tree(n);
  return n;
}

struct Node* internalAddLeft(struct Node* node)
  //@ requires tree(node);
  //@ ensures tree(node) &*& tree(result);
  

  

{
    //@ open tree(node);
    //@ open Node(node, ?l0, ?r0, ?p0, ?c0);
    struct Node* child = internalCreate(node);
    //@ open tree(child);
    //@ open Node(child, ?cl, ?cr, ?cp, ?cc);
    node->left = child;
    //@ close Node(child, cl, cr, cp, cc);
    //@ close tree(child);
    //@ close Node(node, child, r0, p0, c0);
    fix(node);
    //@ open tree(child);
    //@ close tree(child);
    //@ close tree(node);
    return child;
}

void fix(struct Node* node)
  //@ requires tree(node);
  //@ ensures tree(node);
     
  
{
  //@ open tree(node);
  //@ open Node(node, ?l, ?r, ?p, ?c);
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  
  struct Node* parent = node->parent;
  if(parent==0){
    //@ close Node(node, l, r, p, tmp + 1);
    //@ close tree(l);
    //@ close tree(r);
    //@ close tree(node);
  } else {
    //@ close Node(node, l, r, p, tmp + 1);
    //@ close tree(l);
    //@ close tree(r);
    //@ close tree(node);
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
  
  int c = n->count;
  
  return c;
}