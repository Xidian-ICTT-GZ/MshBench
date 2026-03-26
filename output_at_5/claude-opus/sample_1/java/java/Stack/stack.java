class Node {
    Node nxt;
    int val;

    /*@
    predicate nodes() = this |-> nxt &*& this.val |-> val;
    @*/

    Node(Node n, int v)
        //@ requires true;
        //@ ensures nodes();
    {
        nxt = n;
        val = v;
    }

    Node getNext()
        //@ requires nodes();
        //@ ensures nodes() &*& result == nxt;
    {
        return nxt;
    }

    int getValue()
        //@ requires nodes();
        //@ ensures nodes() &*& result == val;
    {
        return val;
    }
}

class Stack {
    private Node head;

    /*@
    predicate stack() = this |-> head &*& (head == null ? true : head.nodes());
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
        //@ requires stack() &*& head != null &*& head.nodes();
        //@ ensures stack();
    {
        int val = head.val;
        Node next = head.getNext();
        head = next;
        return val;
    }
}