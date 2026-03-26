class Node {
    Node nxt;
    int val;

    //@ predicate Node(Node n, int v) = this.nxt |-> n &*& this.val |-> v;

    Node(Node n, int v)
    //@ requires true;
    //@ ensures Node(n, v);
    {
        nxt = n;
        val = v;
    }

    Node getNext()
    //@ requires Node(?n, ?v);
    //@ ensures Node(n, v) &*& result == n;
    {
        return nxt;
    }

    int getValue()
    //@ requires Node(?n, ?v);
    //@ ensures Node(n, v) &*& result == v;
    {
        return val;
    }
}

class Stack {
    private Node head;

    //@ predicate Stack() = head |-> ?h &*& h == null ? emp : Node(h, ?v, ?n);

    //@ predicate Node(Node n, int v, Node nxt) = n.nxt |-> nxt &*& n.val |-> v;

    public Stack()
    //@ requires true;
    //@ ensures Stack();
    {
        head = null;
    }

    public boolean isEmpty()
    //@ requires Stack();
    //@ ensures Stack() &*& result == (head == null);
    {
        return head == null;
    }

    public int pop()
    //@ requires Stack() &*& head != null;
    //@ ensures Stack();
    {
        int val = head.val;
        Node next = head.getNext();
        head = next;
        return val;
    }
}