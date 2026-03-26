/*@ 
predicate tree(struct Node* n; int count) =
  n != 0 ?
    malloc_block_Node(n) &*&
    tree(n->left, ?leftCount) &*&
    tree(n->right, ?rightCount) &*&
    n->parent |-> ?p &*&
    n->count |-> count &*&
    count == 1 + leftCount + rightCount
  :
    true;
@*/

//@ requires true;
//@ ensures tree(result, 1);
struct Node* create();

//@ requires tree(node, ?oldCount);
//@ ensures tree(node, oldCount + 1) &*& tree(result, 1);
struct Node* addLeft(struct Node* node);

//@ requires tree(n, ?count);
//@ ensures tree(n, count) &*& result == count;
int getNbOfNodes(struct Node* n);

//@ requires true;
//@ ensures tree(result, 1);
struct Node* internalCreate(struct Node* parent);

//@ requires tree(node, ?oldCount);
//@ ensures tree(node, oldCount + 1) &*& tree(result, 1);
struct Node* internalAddLeft(struct Node* node);

//@ requires tree(node, ?oldCount) &*& oldCount < INT_MAX;
//@ ensures tree(node, oldCount + 1);
void fix(struct Node* node);

//@ requires true;
//@ ensures false;
void abort();

//@ requires tree(n, ?count);
//@ ensures tree(n, count) &*& result == count;
int internalGetNbOfNodes(struct Node* n);

int main() 
  
  
{
  //@ close tree(0, 0);
  struct Node* mytree = create();
  struct Node* child = addLeft(mytree);
  
  struct Node* child2 = addLeft(child);
  
  int c = getNbOfNodes(child2);
  //@ assert c == 1;
  abort();
}

struct Node* create() 
  
  
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
  //@ close tree(0, 0);
  //@ close tree(0, 0);
  //@ close tree(n, 1);
  
  
  
  return n;
}

struct Node* addLeft(struct Node* node)
  
  
{
  
  
  
  
  
  
  
  
  

  
  

  struct Node* newChild = internalAddLeft(node);
  
  
  
  
  
  
  
  return newChild;
}

int getNbOfNodes(struct Node* n)
  
  
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
  
  
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  //@ close tree(0, 0);
  //@ close tree(0, 0);
  //@ close tree(n, 1);
  
  return n;
}

struct Node* internalAddLeft(struct Node* node)
  

  

{
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    return child;
}

void fix(struct Node* node)
     
  
{
  //@ open tree(node, ?oldCount);
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  //@ close tree(node, tmp + 1);
  
  struct Node* parent = node->parent;
  if(parent==0){
  } else {
    fix(parent);
  }
  
}

void abort()
  
  
{
  while(true)
   
  {
  }
}

int internalGetNbOfNodes(struct Node* n)
  
  
{
  //@ open tree(n, ?count);
  int c = n->count;
  //@ close tree(n, count);
  
  return c;
}