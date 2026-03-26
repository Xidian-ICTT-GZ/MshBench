class Node {
    Node nxt;
    int val;

    //@ predicate Node(Node n, int v) = this.nxt |-> n &*& this.val |-> v;

    Node(Node n, int v)
        //@ requires true;
        //@ ensures this.Node(n, v);
    {
        nxt = n;
        val = v;
    }

    Node getNext()
        //@ requires this.Node(?n, ?v);
        //@ ensures this.Node(n, v) &*& result == n;
    {
        //@ open this.Node(n, v);
        Node r = nxt;
        //@ close this.Node(n, v);
        return r;
    }

    int getValue()
        //@ requires this.Node(?n, ?v);
        //@ ensures this.Node(n, v) &*& result == v;
    {
        //@ open this.Node(n, v);
        int r = val;
        //@ close this.Node(n, v);
        return r;
    }
}

/*@
predicate nodes(Node n;) =
    n == null ? emp : n.Node(?next, ?v) &*& nodes(next);
@*/

class Stack {
    private Node head;

    //@ predicate Stack(boolean empty) = this.head |-> ?h &*& nodes(h) &*& empty == (h == null);

    public Stack()
        //@ requires true;
        //@ ensures this.Stack(true);
    {
        head = null;
        //@ close nodes(null);
        //@ close this.Stack(true);
    }

    public boolean isEmpty()
        //@ requires this.Stack(?e);
        //@ ensures this.Stack(e) &*& result == e;
    {
        //@ open this.Stack(e);
        boolean r = head == null;
        //@ close this.Stack(e);
        return r;
    }

    public int pop()
        //@ requires this.Stack(false);
        //@ ensures this.Stack(_);
    {
        //@ open this.Stack(false);
        //@ open nodes(head);
        //@ open head.Node(?next, ?v);

        int val = head.val;
        //@ close head.Node(next, v);
        Node next = head.getNext();
        //@ open head.Node(next, v);
        head = next;
        //@ close this.Stack(_);
        return val;
    }
}