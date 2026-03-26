/*@ predicate tree(struct Node* n; int c) =
  n != 0 ?
    n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> ?p &*& n->count |-> c &*&
    (l == 0 ? true : tree(l, ?cl)) &*&
    (r == 0 ? true : tree(r, ?cr)) &*&
    c == 1 + (l == 0 ? 0 : cl) + (r == 0 ? 0 : cr)
  :
    false;
@*/

/*@ predicate valid_tree(struct Node* root) =
  root != 0 ?
    tree(root, ?c) &*&
    root->parent |-> 0
  :
    false;
@*/

//@ requires true;
//@ ensures valid_tree(result);
struct Node* create();

//@ requires valid_tree(node) &*& node->left |-> 0;
//@ ensures valid_tree(node) &*& tree(result, 1) &*& result->parent |-> node;
struct Node* addLeft(struct Node* node);

//@ requires tree(n, c);
//@ ensures result == c;
int getNbOfNodes(struct Node* n);

//@ requires true;
//@ ensures tree(result, 1) &*& result->parent |-> parent;
struct Node* internalCreate(struct Node* parent);

//@ requires valid_tree(node) &*& node->left |-> 0;
//@ ensures valid_tree(node) &*& tree(result, 1) &*& result->parent |-> node;
struct Node* internalAddLeft(struct Node* node);

//@ requires tree(node, ?oldc) &*& oldc < INT_MAX;
//@ ensures tree(node, oldc + 1);
void fix(struct Node* node);

//@ requires true;
//@ ensures false;
void abort();

//@ requires tree(n, c);
//@ ensures result == c;
int internalGetNbOfNodes(struct Node* n);

int main() 
{
  struct Node* mytree = create();
  struct Node* child = addLeft(mytree);
  
  struct Node* child2 = addLeft(child);
  
  int c = getNbOfNodes(child2);
  //@ assert c == 1;
  abort();
}

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

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
{
  while(true)
  {
  }
}

int internalGetNbOfNodes(struct Node* n)
{
  int c = n->count;
  return c;
}