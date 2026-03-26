/*@ predicate node(struct Node *n; int count, struct Node *parent, struct Node *left, struct Node *right) =
    n != 0 &*&
    malloc_block_Node(n) &*&
    n->count |-> count &*&
    n->parent |-> parent &*&
    n->left |-> left &*&
    n->right |-> right &*&
    (left == 0 || parent == n) &*&
    (right == 0 || parent == n);
@*/

/*@ predicate tree(struct Node *root; int total_count) =
    root == 0 ? total_count == 0 :
    node(root, total_count, 0, ?l, ?r) &*&
    (l == 0 || tree(l, ?l_count)) &*&
    (r == 0 || tree(r, ?r_count)) &*&
    total_count == 1 + (l == 0 ? 0 : l_count) + (r == 0 ? 0 : r_count);
@*/

/*@ lemma void tree_validity(struct Node *n; int c)
    requires node(n, c, ?, ?, ?) &*& c > 0;
    ensures node(n, c, ?, ?, ?);
@*/
/*@ proof {
    // trivial: just restate the precondition
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

/*@ requires node(node, ?c, ?, ?, ?) &*& c >= 1;
    ensures node(result, 1, node, 0, 0) &*& node(node, c + 1, ?, ?, ?);
@*/
struct Node *addLeft(struct Node *node)
{
  struct Node *newChild = internalAddLeft(node);

  return newChild;
}

/*@ requires node(n, ?c, ?, ?, ?) &*& c >= 1;
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

/*@ requires node(node, ?c, ?, ?, ?) &*& c >= 1;
    ensures node(result, 1, node, 0, 0) &*& node(node, c + 1, ?, ?, ?);
@*/
struct Node *internalAddLeft(struct Node *node)
{
  struct Node *child = internalCreate(node);
  node->left = child;
  fix(node);
  return child;
}

/*@ requires node(node, ?c, ?, ?, ?) &*& c >= 1 &*& c < INT_MAX;
    ensures node(node, c + 1, ?, ?, ?);
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

/*@ requires node(n, ?c, ?, ?, ?) &*& c >= 1;
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