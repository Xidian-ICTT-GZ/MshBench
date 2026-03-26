/*@ predicate node(struct Node *n; int count, struct Node *parent, struct Node *left, struct Node *right) =
    n != 0 &*&
    malloc_block_Node(n) &*&
    n->count |-> count &*&
    n->parent |-> parent &*&
    n->left |-> left &*&
    n->right |-> right;
@*/

/*@ predicate tree(struct Node *root; int total_count) =
    root == 0 ?
        total_count == 0
    :
        node(root, total_count, 0, ?l_child, ?r_child) &*&
        (l_child == 0 || exist<int>(?l_count &*& tree(root->left, l_count))) &*&
        (r_child == 0 || exist<int>(?r_count &*& tree(root->right, r_count))) &*&
        total_count == 1 + (l_child == 0 ? 0 : root->left->count) + (r_child == 0 ? 0 : root->right->count);
@*/

/*@ lemma void tree_validity(struct Node *n; int c)
    requires node(n, c, _, _, _) &*& c > 0;
    ensures node(n, c, _, _, _);
@*/
/*@ proof {
    // trivial
} @*/

/*@ requires true;
    ensures node(result, 1, 0, 0, 0);
@*/
struct Node *create()

{
  struct Node *n = malloc(sizeof(struct Node));
  if (n == 0)
  {
    abort();
  }
  else
  {
  }
  n->parent = 0;
  n->left = 0;
  n->right = 0;
  n->count = 1;

  return n;
}

/*@ requires node(node, ?c, _, _, _) &*& c >= 1;
    ensures node(result, 1, node, 0, 0) &*& node(node, c + 1, _, _, _);
@*/
struct Node *addLeft(struct Node *node)

{

  struct Node *newChild = internalAddLeft(node);

  return newChild;
}

/*@ requires node(n, ?c, _, _, _) &*& c >= 1;
    ensures result == c;
@*/
int getNbOfNodes(struct Node *n)

{

  int c = internalGetNbOfNodes(n);

  return c;
}

struct Node
{
  struct Node *left;
  struct Node *right;
  struct Node *parent;
  int count;
};

/*@ requires true;
    ensures node(result, 1, parent, 0, 0);
@*/
struct Node *internalCreate(struct Node *parent)

{
  struct Node *n = malloc(sizeof(struct Node));
  if (n == 0)
  {
    abort();
  }
  else
  {
  }
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;

  return n;
}

/*@ requires node(node, ?c, _, _, _) &*& c >= 1;
    ensures node(result, 1, node, 0, 0) &*& node(node, c + 1, _, _, _);
@*/
struct Node *internalAddLeft(struct Node *node)

{
  struct Node *child = internalCreate(node);
  node->left = child;
  fix(node);
  return child;
}

/*@ requires node(node, ?c, _, _, _) &*& c >= 1 &*& c < INT_MAX;
    ensures node(node, c + 1, _, _, _);
@*/
void fix(struct Node *node)

{
  int tmp = node->count;
  if (tmp == INT_MAX)
  {
    abort();
  }
  node->count = tmp + 1;

  struct Node *parent = node->parent;
  if (parent == 0)
  {
  }
  else
  {
    fix(parent);
  }
}

void abort()

{
  while (true)

  {
  }
}

/*@ requires node(n, ?c, _, _, _) &*& c >= 1;
    ensures result == c;
@*/
int internalGetNbOfNodes(struct Node *n)

{

  int c = n->count;

  return c;
}

/*@ requires true;
    ensures true;
@*/
int main()

{
  struct Node *mytree = create();
  struct Node *child = addLeft(mytree);

  struct Node *child2 = addLeft(child);

  int c = getNbOfNodes(child2);
  assert(c == 1);
  abort();
}