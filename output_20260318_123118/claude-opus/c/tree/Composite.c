struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

/*@ predicate node(struct Node* n, struct Node* parent; int count) =
      n != 0 &*&
      n->parent |-> parent &*&
      n->count |-> count &*&
      n->left |-> ?l &*&
      n->right |-> ?r &*&
      node_or_null(l, n) &*& node_or_null(r, n);
@*/

/*@ predicate node_or_null(struct Node* n, struct Node* parent) =
      n == 0 ? true : node(n, parent, ?c);
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
    fix(parent);
  }
}

struct Node* internalAddLeft(struct Node* node)
  //@ requires node(node, ?parent, ?count) &*& count >= 1;
  //@ ensures node(node, parent, count + 1) &*& node(result, node, 1);
{
  struct Node* child = internalCreate(node);
  node->left = child;
  fix(node);
  return child;
}

int internalGetNbOfNodes(struct Node* n)
  //@ requires node(n, ?parent, ?count);
  //@ ensures node(n, parent, count) &*& result == count;
{
  int c = n->count;
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
  return n;
}

struct Node* addLeft(struct Node* node)
  //@ requires node(node, ?parent, ?count) &*& count >= 1;
  //@ ensures node(node, parent, count + 1) &*& node(result, node, 1);
{
  struct Node* newChild = internalAddLeft(node);
  return newChild;
}

int getNbOfNodes(struct Node* n)
  //@ requires node(n, ?parent, ?count);
  //@ ensures node(n, parent, count) &*& result == count;
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
  //@ assert c == 1;
  assert(c==1);
  abort();
}