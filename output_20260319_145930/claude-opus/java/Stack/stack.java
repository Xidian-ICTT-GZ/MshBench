/*@
predicate Node_fields(Node node; Node nxt, int val) =
    node.nxt |-> nxt &*& node.val |-> val;

predicate lseg(Node from, Node to;) =
    from == to ?
        emp
    :
        Node_fields(from, ?next, ?v) &*& lseg(next, to);

predicate Stack_inv(Stack s;) =
    s.head |-> ?h &*& lseg(h, null);
@*/

class Node {
    Node nxt;
    int val;

    Node(Node n, int v)
        //@ requires true;
        //@ ensures Node_fields(this, n, v);
    {
        nxt = n;
        val = v;
        //@ close Node_fields(this, n, v);
    }

    Node getNext()
        //@ requires Node_fields(this, ?n, ?v);
        //@ ensures Node_fields(this, n, v) &*& result == n;
    {
        //@ open Node_fields(this, n, v);
        Node r = nxt;
        //@ close Node_fields(this, n, v);
        return r;
    }

    int getValue()
        //@ requires Node_fields(this, ?n, ?v);
        //@ ensures Node_fields(this, n, v) &*& result == v;
    {
        //@ open Node_fields(this, n, v);
        int r = val;
        //@ close Node_fields(this, n, v);
        return r;
    }
}

class Stack {
    private Node head;

    public Stack()
        //@ requires true;
        //@ ensures Stack_inv(this);
    {
        head = null;
        //@ close lseg(null, null);
        //@ close Stack_inv(this);
    }

    public boolean isEmpty()
        //@ requires Stack_inv(this);
        //@ ensures Stack_inv(this) &*& result == (old_head == null) &*& this.head |-> old_head &*& lseg(old_head, null);
    {
        //@ open Stack_inv(this);
        boolean r = head == null;
        //@ close Stack_inv(this);
        return r;
    }

    public int pop()
        //@ requires Stack_inv(this) &*& this.head |-> ?h &*& h != null &*& lseg(h, null);
        //@ ensures Stack_inv(this);
    {
        //@ open Stack_inv(this);
        //@ open lseg(head, null);

        int val = head.val;
        //@ open Node_fields(head, ?next, ?v);
        Node next = head.nxt;
        //@ close Node_fields(head, next, v);
        //@ open Node_fields(head, next, v);
        head = next;
        //@ close Stack_inv(this);
        return val;
    }
}