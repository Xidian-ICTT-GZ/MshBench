class Node {
Node nxt;
int val;

//@ requires true;
//@ ensures this.nxt == n &*& this.val == v;
Node(Node n, int v) {
    nxt = n;        val = v;
}

//@ requires this != null;
//@ ensures result == this.nxt &*& this.nxt |-> _;
Node getNext() {
    return nxt;
}

//@ requires this != null;
//@ ensures result == this.val &*& this.val |-> _;
int getValue() {
    return val;
}

/*@ predicate node(Node n; int v, Node next) =
    n != null &*& n.val |-> v &*& n.nxt |-> next;
@*/
}

class Stack {
    private Node head;

    /*@ predicate stack(Stack s; Node h) =
        s.head |-> h &*& (h == null ? true : Node.node(h; ?v, ?n) &*& stack(s; n));
    @*/
    
    //@ requires true;
    //@ ensures stack(this, null) &*& head == null;
    public Stack() {
        head = null;
    }

    //@ requires stack(this, ?h);
    //@ ensures stack(this, h) &*& result == (h == null);
    public boolean isEmpty() {
        return head == null;
    }

    //@ requires stack(this, ?h) &*& h != null &*& Node.node(h; ?v, ?next);
    //@ ensures stack(this, next) &*& result == v;
    public int pop() {
        int val = head.val;
        Node next = head.getNext();
        head = next;
        return val;
    }
}