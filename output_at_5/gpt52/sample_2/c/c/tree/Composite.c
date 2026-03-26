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
  //@ assert c == 1;
  assert(c==1);
  abort();
}

struct Node* create() 
  //@ requires true;
  //@ ensures tree(result) &*& Node(result, 0, 0, 0, 1);
  
  
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
  //@ close Node(n, 0, 0, 0, 1);
  return n;
}

struct Node* addLeft(struct Node* node)
  //@ requires tree(node);
  //@ ensures tree(node) &*& tree(result) &*& Node(result, 0, 0, node, 1);
  
  
{
  
  
  
  
  
  
  
  
  

  
  

  struct Node* newChild = internalAddLeft(node);
  
  
  
  
  
  
  
  return newChild;
}

int getNbOfNodes(struct Node* n)
  //@ requires Node(n, ?l, ?r, ?p, ?c);
  //@ ensures Node(n, l, r, p, c) &*& result == c;
  
  
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
  //@ ensures tree(result) &*& Node(result, 0, 0, parent, 1);
  
  
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
  //@ close Node(n, 0, 0, parent, 1);
  return n;
}

struct Node* internalAddLeft(struct Node* node)
  //@ requires tree(node);
  //@ ensures tree(node) &*& tree(result) &*& Node(result, 0, 0, node, 1);
  

  

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
    //@ close tree(l0);
    //@ close tree(r0);
    //@ close tree(node);
    //@ close Node(child, 0, 0, node, 1);
    return child;
}

void fix(struct Node* node)
  //@ requires true;
  //@ ensures true;
     
  
{
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  
  struct Node* parent = node->parent;
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
  
  int c = n->count;
  
  return c;
}