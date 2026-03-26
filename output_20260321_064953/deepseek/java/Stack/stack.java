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
        //@ close Node(n, v);
    }

    Node getNext()
        //@ requires Node(?n, ?v);
        //@ ensures Node(n, v) &*& result == n;
    {
        //@ open Node(n, v);
        return nxt;
        //@ close Node(n, v);
    }

    int getValue()
        //@ requires Node(?n, ?v);
        //@ ensures Node(n, v) &*& result == v;
    {
        //@ open Node(n, v);
        return val;
        //@ close Node(n, v);
    }
}

class Stack {
    private Node head;

    /*@
    predicate Stack() = head |-> ?h &*& h == null ? true : h.Node(_, _);
    @*/

    public Stack()
        //@ requires true;
        //@ ensures Stack();
    {
        head = null;
        //@ close Stack();
    }

    public boolean isEmpty()
        //@ requires Stack();
        //@ ensures Stack() &*& result == (head == null);
    {
        //@ open Stack();
        boolean result = head == null;
        //@ close Stack();
        return result;
    }

    public int pop()
        //@ requires Stack() &*& head != null;
        //@ ensures Stack();
    {
        //@ open Stack();
        //@ open head.Node(_, _);
        int val = head.val;
        Node next = head.getNext();
        head = next;
        //@ close Stack();
        return val;
    }
}