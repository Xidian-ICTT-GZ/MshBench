#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>

/*@ predicate node(struct node *n; struct node *l, struct node *r, struct node *p, int c) =
    n != 0 &*&
    n->left |-> l &*&
    n->right |-> r &*&
    n->parent |-> p &*&
    n->count |-> c &*&
    malloc_block_node(n);
@*/

/*@ predicate tree(struct node *root; int count) =
    root == 0 ? count == 0 :
    node(root; ?l, ?r, ?p, ?c) &*&
    tree(l; ?lc) &*&
    tree(r; ?rc) &*&
    count == c &*&
    c == 1 + lc + rc;
@*/

/*@ predicate tree_root(struct node *root; int count) =
    root != 0 &*&
    tree(root; count);
@*/

/*@ lemma void subtree_get_count_correct(struct node *node; int count)
  requires node(node; ?l, ?r, ?p, count);
  ensures result == count;
{
  open node(node; l, r, p, count);
  close node(node; l, r, p, count);
}
@*/

/*@ lemma void subtree_get_count_null()
  requires node == 0;
  ensures result == 0;
{
}
@*/

struct node
{
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

struct node *create_node(struct node *p)

/*@ requires p == 0 || node(p; ?_, ?_, ?_, ?_);
    ensures node(result; 0, 0, p, 1);
@*/
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0)
  {
    abort();
  }
  n->left = 0;
  n->right = 0;
  n->parent = p;
  n->count = 1;

  return n;
}

struct node *create_tree()

/*@ requires true;
    ensures tree_root(result; 1);
@*/
{
  struct node *n = create_node(0);

  return n;
}

int subtree_get_count(struct node *node)

/*@ requires node == 0 || node(node; ?l, ?r, ?p, ?c);
    ensures result == (node == 0 ? 0 : c);
@*/
{
  int result = 0;

  if (node != 0)
  {
    result = node->count;
  }

  return result;
}

void fixup_ancestors(struct node *n, struct node *p, int count)

/*@ requires
      (n == 0 && p == 0) ||
      (n != 0 && p != 0 && node(p; ?pl, ?pr, ?pp, ?pc) &*&
       (n == pl ==> node(n; ?nl, ?nr, p, count) &*& tree(nl; ?nlc) &*& tree(nr; ?nrc) &*& count == 1 + nlc + nrc) &
       (n == pr ==> node(n; ?nl, ?nr, p, count) &*& tree(nl; ?nlc) &*& tree(nr; ?nrc) &*& count == 1 + nlc + nrc)) &
      (p != 0 ==> p != 0 &*& node(pp; ?_, ?_, ?_, ?_));
    ensures
      (p == 0) ||
      (p != 0 &*& node(p; ?pl2, ?pr2, ?pp2, ?newc) &*& newc == 1 + subtree_get_count(pl2) + subtree_get_count(pr2) &*&
       (pl2 != 0 ==> node(pl2; ?_, ?_, p, ?_) &*& tree(pl2; ?plc)) &
       (pr2 != 0 ==> node(pr2; ?_, ?_, p, ?_) &*& tree(pr2; ?prc)));
@*/
{
  if (p == 0)
  {
  }
  else
  {
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left)
    {

      leftCount = count;
      rightCount = subtree_get_count(right);
    }
    else
    {
      leftCount = subtree_get_count(left);
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount)
    {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      fixup_ancestors(p, grandparent, pcount);
    }
  }
}

struct node *tree_add_left(struct node *node)

/*@ requires node(node; ?l, ?r, ?p, ?c) &*& tree(l; ?lc) &*& tree(r; ?rc) &*& c == 1 + lc + rc;
    ensures node(result; 0, 0, node, 1) &*& node(node; result, ?r2, ?p2, ?c2) &*& c2 == 1 + 1 + rc;
@*/
{

  struct node *n = create_node(node);

  {
    struct node *nodeLeft = node->left;

    node->left = n;

    fixup_ancestors(n, node, 1);
  }

  return n;
}

struct node *tree_add_right(struct node *node)

/*@ requires node(node; ?l, ?r, ?p, ?c) &*& tree(l; ?lc) &*& tree(r; ?rc) &*& c == 1 + lc + rc;
    ensures node(result; 0, 0, node, 1) &*& node(node; ?l2, result, ?p2, ?c2) &*& c2 == 1 + lc + 1;
@*/
{

  struct node *n = create_node(node);

  {
    struct node *nodeRight = node->right;

    node->right = n;

    fixup_ancestors(n, node, 1);
  }

  return n;
}

struct node *tree_get_parent(struct node *node)

/*@ requires node(node; ?l, ?r, ?p, ?c);
    ensures result == p;
@*/
{

  struct node *p = node->parent;

  return p;
}

void subtree_dispose(struct node *node)

/*@ requires node == 0 || node(node; ?l, ?r, ?p, ?c) &*& tree(l; ?lc) &*& tree(r; ?rc);
    ensures node == 0;
@*/
{

  if (node != 0)
  {
    {
      struct node *left = node->left;
      subtree_dispose(left);
    }
    {
      struct node *right = node->right;
      subtree_dispose(right);
    }
    free(node);
  }
}

void tree_dispose(struct node *node)

/*@ requires node == 0 || tree(node; ?c);
    ensures node == 0;
@*/
{

  subtree_dispose(node);
}

int main0()

/*@ requires true;
    ensures true;
@*/
{
  struct node *node = create_tree();
  node = tree_add_left(node);
  node = tree_add_right(node);
  node = tree_get_parent(node);
  node = tree_add_left(node);
  node = tree_get_parent(node);
  node = tree_get_parent(node);
  tree_dispose(node);
  return 0;
}

int main()

/*@ requires true;
    ensures true;
@*/
{
  struct node *root = create_tree();
  struct node *left = tree_add_left(root);
  struct node *leftRight = tree_add_right(left);
  struct node *leftRightParent = tree_get_parent(leftRight);

  struct node *leftLeft = tree_add_left(left);

  struct node *leftRightRight = tree_add_right(leftRight);

  tree_dispose(root);
  return 0;
}