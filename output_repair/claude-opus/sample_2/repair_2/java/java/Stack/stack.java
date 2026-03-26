/*@ predicate StackList(Node n, int count) =
      (n == null &*& count == 0) ||
      (n != null &*& count > 0 &*& n.val |-> _ &*& n.nxt |-> ?nx &*& StackList(nx, count - 1));
@*/

class Node {
    Node nxt;
    int val;

    //@ requires true;
    //@ ensures this.val |-> v &*& this.nxt |-> n;
    Node(Node n, int v)
    {
        nxt = n;
        val = v;
    }

    //@ requires this.nxt |-> ?nx;
    //@ ensures this.nxt |-> nx &*& result == nx;
    Node getNext()
    {
        return nxt;
    }

    //@ requires this.val |-> ?v;
    //@ ensures this.val |-> v &*& result == v;
    int getValue()
    {
        return val;
    }
}

class Stack {
    private Node head;

    //@ requires true;
    //@ ensures this.head |-> null;
    public Stack()
    {
        head = null;
    }

    //@ requires this.head |-> ?h;
    //@ ensures this.head |-> h &*& result == (h == null);
    public boolean isEmpty()
    {
        return head == null;
    }

    //@ requires this.head |-> ?h &*& h != null &*& h.val |-> ?v &*& h.nxt |-> ?nx;
    //@ ensures this.head |-> nx &*& result == v;
    public int pop()
    {
        int val = head.val;
        Node next = head.getNext();
        head = next;
        return val;
    }
}