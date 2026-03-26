class Node {
    Node nxt;
    int val;

    /*@ predicate node(Node n; Node nxt, int val) =
            n.nxt |-> nxt &*& n.val |-> val;
    @*/

    Node(Node n, int v)
    //@ requires true;
    //@ ensures node(this, n, v);
    {
        nxt = n;
        val = v;
    }

    Node getNext()
    //@ requires node(this, ?nxt, ?val);
    //@ ensures node(this, nxt, val) &*& result == nxt;
    {
        return nxt;
    }

    int getValue()
    //@ requires node(this, ?nxt, ?val);
    //@ ensures node(this, nxt, val) &*& result == val;
    {
        return val;
    }
}

class Stack {
    private Node head;

    /*@ predicate nodes(Node n) =
            n == null ?
                emp
            :
                n.nxt |-> ?nxt &*& n.val |-> ?val &*& nodes(nxt);
    @*/

    /*@ predicate stack(Stack s; Node h) =
            s.head |-> h &*& nodes(h);
    @*/

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
    //@ requires stack(this, ?h) &*& h != null;
    //@ ensures stack(this, ?h2);
    {
        int val = head.val;
        Node next = head.getNext();
        head = next;

        return val;
    }
}