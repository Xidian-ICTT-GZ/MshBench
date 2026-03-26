class Node {
    Node nxt;
    int val;

    /*@
    predicate node() = this.nxt |-> nxt &*& this.val |-> val;
    @*/

    Node(Node n, int v)
        //@ requires true;
        //@ ensures node();
    {
        nxt = n;
        val = v;
    }

    Node getNext()
        //@ requires node();
        //@ ensures node() &*& result == nxt;
    {
        return nxt;
    }

    int getValue()
        //@ requires node();
        //@ ensures node() &*& result == val;
    {
        return val;
    }
}

class Stack {
    private Node head;

    /*@
    predicate nodes(Node n) = n == null ? true : n.node() &*& nodes(n.nxt);
    predicate stack() = this.head |-> head &*& nodes(head);
    @*/

    public Stack()
        //@ requires true;
        //@ ensures stack();
    {
        head = null;
    }

    public boolean isEmpty()
        //@ requires stack();
        //@ ensures stack() &*& result == (head == null);
    {
        return head == null;
    }

    public int pop()
        //@ requires stack() &*& head != null;
        //@ ensures stack();
    {
        //@ open stack();
        //@ open nodes(head);
        int val = head.val;
        Node next = head.getNext();
        head = next;
        //@ close nodes(head);
        //@ close stack();
        return val;
    }
}