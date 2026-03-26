struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

/*@
predicate node(struct Node* n; int c) =
  n->count |-> c &*&
  n->parent |-> ?p &*&
  n->left |-> ?l &*& n->right |-> ?r &*&
  (l == 0 ? true : node(l, _)) &*&
  (r == 0 ? true : node(r, _)) &*&
  (p == 0 ? true : true);
@*/

struct Node* create()
  //@ requires true;
  //@ ensures node(result, 1);
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
  
  //@ close node(n,1);
  return n;
}

struct Node* internalCreate(struct Node* parent)
  //@ requires true;
  //@ ensures node(result, 1);
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  
  //@ close node(n,1);
  return n;
}

void fix(struct Node* node)
  //@ requires node(node, ?c);
  //@ ensures node(node, c + 1);
{
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  
  struct Node* parent = node->parent;
  if(parent==0){
    //@ close node(node, tmp + 1);
  } else {
    //@ open node(node, _);
    //@ open node(parent, ?pc);
    fix(parent);
    //@ close node(parent, pc + 1);
    //@ close node(node, tmp + 1);
  }
}

struct Node* internalAddLeft(struct Node* node)
  //@ requires node(node, ?c);
  //@ ensures node(node, c + 1) &*& node(result, 1);
{
  struct Node* child = internalCreate(node);
  node->left = child;
  fix(node);
  //@ close node(child, 1);
  return child;
}

struct Node* addLeft(struct Node* node)
  //@ requires node(node, ?c);
  //@ ensures node(node, c + 1) &*& node(result, 1);
{
  struct Node* newChild = internalAddLeft(node);
  return newChild;
}

int internalGetNbOfNodes(struct Node* n)
  //@ requires node(n, ?c);
  //@ ensures node(n, c) &*& result == c;
{
  int c = n->count;
  return c;
}

int getNbOfNodes(struct Node* n)
  //@ requires node(n, ?c);
  //@ ensures node(n, c) &*& result == c;
{
  int c = internalGetNbOfNodes(n);
  return c;
}

int main() 
  //@ requires true;
  //@ ensures false;
{
  struct Node* mytree = create();
  struct Node* child = addLeft(mytree);
  struct Node* child2 = addLeft(child);
  int c = getNbOfNodes(child2);
  //@ open node(child2, _);
  //@ open node(child, _);
  //@ open node(mytree, _);
  assert(c==1);
  abort();
}

void abort()
  //@ requires true;
  //@ ensures false;
{
  while(true)
  {
  }
}