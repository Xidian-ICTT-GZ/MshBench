struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

/*@ predicate nodes(struct Node* n, int c) =
      n == 0 ?
        c == 0
      :
        malloc_block_Node(n) &*&
        n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> ?p &*& n->count |-> ?count_n &*&
        nodes(l, ?cl) &*& nodes(r, ?cr) &*&
        c == count_n &*&
        count_n == 1 + cl + cr;
@*/

struct Node* create()
  //@ requires true;
  //@ ensures nodes(result, 1);
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0){
    abort();
  } else {}
  n->parent = 0;
  n->left = 0;
  n->right = 0;
  n->count = 1;
  return n;
}

struct Node* internalCreate(struct Node* parent)
  //@ requires true;
  //@ ensures nodes(result, 1) &*& result->parent |-> parent;
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
  //@ requires nodes(node, ?c) &*& c < INT_MAX;
  //@ ensures nodes(node, c + 1);
{
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;
  
  struct Node* parent = node->parent;
  if(parent==0){
    //@ close nodes(node, tmp + 1);
  } else {
    //@ open nodes(node, tmp);
    fix(parent);
    //@ open nodes(parent, ?cp);
    //@ close nodes(node, tmp + 1);
  }
}

struct Node* internalAddLeft(struct Node* node)
  //@ requires nodes(node, ?c);
  //@ ensures nodes(result, 1) &*& nodes(node, c + 1);
{
  struct Node* child = internalCreate(node);
  node->left = child;
  fix(node);
  return child;
}

struct Node* addLeft(struct Node* node)
  //@ requires nodes(node, ?c);
  //@ ensures nodes(result, 1) &*& nodes(node, c + 1);
{
  struct Node* newChild = internalAddLeft(node);
  return newChild;
}

int internalGetNbOfNodes(struct Node* n)
  //@ requires nodes(n, ?c);
  //@ ensures nodes(n, c) &*& result == c;
{
  int c = n->count;
  return c;
}

int getNbOfNodes(struct Node* n)
  //@ requires nodes(n, ?c);
  //@ ensures nodes(n, c) &*& result == c;
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
  //@ assert c == 1;
  assert(c==1);
  abort();
}