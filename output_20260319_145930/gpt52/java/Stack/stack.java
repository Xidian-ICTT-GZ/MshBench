class Node {
    Node nxt;
    int val;

    /*@
    predicate node(Node n; Node nxt, int val) =
        n.nxt |-> nxt &*& n.val |-> val;
    @*/

    //@ requires this.nxt |-> _ &*& this.val |-> _;
    //@ ensures node(this; n, v);
    Node(Node n, int v)
    {
        nxt = n;
        val = v;
    }

    //@ requires node(this; ?nxt, ?val);
    //@ ensures node(this; nxt, val) &*& result == nxt;
    Node getNext()
    {
        //@ open node(this; nxt, val);
        Node r = nxt;
        //@ close node(this; nxt, val);
        return r;
    }

    //@ requires node(this; ?nxt, ?val);
    //@ ensures node(this; nxt, val) &*& result == val;
    int getValue()
    {
        //@ open node(this; nxt, val);
        int r = val;
        //@ close node(this; nxt, val);
        return r;
    }
}

class Stack {
    private Node head;

    /*@
    predicate nodes(Node n) =
        n == null ?
            true
        :
            node(n; ?nxt, ?v) &*& nodes(nxt);

    predicate stack(Stack s; Node h) =
        s.head |-> h &*& nodes(h);
    @*/

    //@ requires this.head |-> _;
    //@ ensures stack(this; null);
    public Stack()
    {
        head = null;
        //@ close nodes(null);
        //@ close stack(this; null);
    }

    //@ requires stack(this; ?h);
    //@ ensures stack(this; h) &*& result == (h == null);
    public boolean isEmpty()
    {
        //@ open stack(this; h);
        boolean r = head == null;
        //@ close stack(this; h);
        return r;
    }

    //@ requires stack(this; ?h) &*& h != null;
    //@ ensures stack(this; ?h2) &*& result == ?v;
    public int pop()
    {
        //@ open stack(this; h);
        //@ open nodes(h);
        //@ open node(h; ?nxt, ?v);

        int val = head.val;
        Node next = head.getNext();
        head = next;

        //@ close node(h; nxt, v);
        //@ close nodes(nxt);
        //@ close stack(this; nxt);

        return val;
    }
}