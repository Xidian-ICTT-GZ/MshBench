struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

/*@ predicate node(struct Node* n, struct Node* parent; int count) =
      n != 0 &*& n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> parent &*& n->count |-> count
      &*& (l == 0 ? true : node(l, n, _))
      &*& (r == 0 ? true : node(r, n, _));
@*/

struct Node* internalCreate(struct Node* parent)
  //@ requires true;
  //@ ensures node(result, parent, 1);
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  
  //@ close node(n, parent, 1);
  return n;
}

void fix(struct Node* node)
  //@ requires node(node, ?parent, ?count);
  //@ ensures node(node, parent, count + 1);
{
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  
  struct Node* parent = node->parent;
  if(parent==0){
  } else {
    //@ open node(parent, ?grandparent, ?parentCount);
    fix(parent);
    //@ close node(parent, grandparent, parentCount + 1);
  }
  //@ open node(node, parent, tmp);
  //@ close node(node, parent, tmp+1);
}

struct Node* internalAddLeft(struct Node* node)
  //@ requires node(node, ?parent, ?count);
  //@ ensures node(node, parent, count + 1) &*& node(result, node, 1) &*& node != 0 &*& result == node->left;
{
    //@ open node(node, parent, count);
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    //@ close node(node, parent, count + 1);
    //@ close node(child, node, 1);
    return child;
}

int internalGetNbOfNodes(struct Node* n)
  //@ requires node(n, _, ?count);
  //@ ensures node(n, _, count) &*& result == count;
{
  int c = n->count;
  //@ assert c == n->count;
  return c;
}

struct Node* create() 
  //@ requires true;
  //@ ensures node(result, 0, 1);
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
  
  //@ close node(n, 0, 1);
  return n;
}

struct Node* addLeft(struct Node* node)
  //@ requires node(node, ?parent, ?count);
  //@ ensures node(node, parent, count + 1) &*& node(result, node, 1) &*& result == node->left;
{
  struct Node* newChild = internalAddLeft(node);
  return newChild;
}

int getNbOfNodes(struct Node* n)
  //@ requires node(n, _, ?count);
  //@ ensures node(n, _, count) &*& result == count;
{
  int c = internalGetNbOfNodes(n);
  return c;
}

void abort()
  //@ requires true;
  //@ ensures false;
{
  while(true)
  {
  }
}

int main()
  //@ requires true;
  //@ ensures false;
{
  struct Node* mytree = create();
  struct Node* child = addLeft(mytree);
  struct Node* child2 = addLeft(child);
  int c = getNbOfNodes(child2);
  assert(c==1);
  abort();
}