class Node {
  //@ predicate node(Node n; Node nxt, int val) =
  //@     n != null &*& n.nxt |-> nxt &*& n.val |-> val;

  Node nxt;
  int val;

  Node(Node n, int v)
    //@ requires true;
    //@ ensures node(this, n, v);
  {
    nxt = n;
    val = v;
  }

  Node getNext()
    //@ requires node(this, ?nxt, ?v);
    //@ ensures node(this, nxt, v) &*& result == nxt;
  {
    return nxt;
  }

  int getValue()
    //@ requires node(this, ?nxt, ?v);
    //@ ensures node(this, nxt, v) &*& result == v;
  {
    return val;
  }
}

class Stack {
  private Node head;

  //@ predicate stack(Stack s; Node headNode) =
  //@     s.head |-> headNode &*& (headNode == null ? true : node(headNode, ?nxt, ?v));

  public Stack()
    //@ requires true;
    //@ ensures stack(this, null);
  {
    head = null;
  }

  public boolean isEmpty()
    //@ requires stack(this, ?h);
    //@ ensures stack(this, h) &*& result == (h == null);
  {
    return head == null;
  }

  public int pop()
    //@ requires stack(this, ?h) &*& h != null &*& node(h, ?nxt, ?v);
    //@ ensures stack(this, nxt) &*& result == v;
  {
    int val = head.val;
    Node next = head.getNext();
    head = next;

    return val;
  }
}