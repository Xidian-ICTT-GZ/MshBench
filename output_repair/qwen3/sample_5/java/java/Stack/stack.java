/*@ predicate NodeList(Node n, int count) =
      n == null ? count == 0 :
        n.val |-> _ &*& n.nxt |-> ?next &*& NodeList(next, count - 1) &*& count > 0;
@*/

/*@ predicate NodeList(Node n, int count) =
      (n == null &*& count == 0) ||
      (n != null &*& count > 0 &*& n.val |-> _ &*& n.nxt |-> ?next &*& NodeList(next, count - 1));
@*/

class Node {
    Node nxt;
    int val;

    //@ predicate valid(int v, Node nx) = this.val |-> v &*& this.nxt |-> nx;

    /*@
      requires true;
      ensures this.val |-> v &*& this.nxt |-> n;
    @*/
    Node(Node n, int v)
    {
        nxt = n;
        val = v;
    }

    /*@
      requires this.nxt |-> ?nx;
      ensures this.nxt |-> nx &*& result == nx;
    @*/
    Node getNext()
    {
        return nxt;
    }

    /*@
      requires this.val |-> ?v;
      ensures this.val |-> v &*& result == v;
    @*/
    int getValue()
    {
        return val;
    }
}

/*@ predicate StackList(Node n, int count) =
      (n == null &*& count == 0) ||
      (n != null &*& count > 0 &*& n.val |-> _ &*& n.nxt |-> ?nx &*& StackList(nx, count - 1));
@*/

class Stack {
    private Node head;

    //@ predicate valid(int count) = this.head |-> ?h &*& StackList(h, count) &*& count >= 0;

    /*@
      requires true;
      ensures this.head |-> null;
    @*/
    public Stack()
    {
        head = null;
    }

    /*@
      requires this.head |-> ?h;
      ensures this.head |-> h &*& (h == null ? result == true : result == false);
    @*/
    public boolean isEmpty()
    {
        return head == null;
    }

    /*@
      requires this.head |-> ?h &*& h != null &*& h.val |-> ?v &*& h.nxt |-> ?nx &*& StackList(nx, ?c) &*& c >= 0;
      ensures this.head |-> nx &*& StackList(nx, c) &*& result == v;
    @*/
    public int pop()
    {
        int val = head.val;
        Node next = head.getNext();
        head = next;
        return val;
    }
}