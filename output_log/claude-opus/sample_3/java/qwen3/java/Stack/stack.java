class Node {
    Node nxt;
    int val;

    //@ requires true;
    //@ ensures this.nxt |-> n &*& this.val |-> v;
    Node(Node n, int v) {
        nxt = n;
        val = v;
    }

    //@ requires this.nxt |-> ?n;
    //@ ensures this.nxt |-> n &*& result == n;
    Node getNext() {
        return nxt;
    }

    //@ requires this.val |-> ?v;
    //@ ensures this.val |-> v &*& result == v;
    int getValue() {
        return val;
    }
}

/*@ predicate node(Node n; int v, Node next) =
    n != null &*& n.val |-> v &*& n.nxt |-> next;
@*/

class Stack {
    private Node head;

    //@ requires true;
    //@ ensures this.head |-> null;
    public Stack() {
        head = null;
    }

    //@ requires this.head |-> ?h;
    //@ ensures this.head |-> h &*& result == (h == null);
    public boolean isEmpty() {
        return head == null;
    }

    //@ requires this.head |-> ?h &*& h != null &*& h.val |-> ?v &*& h.nxt |-> ?next;
    //@ ensures this.head |-> next &*& result == v;
    public int pop() {
        int val = head.val;
        //@ open this.head |-> _;
        Node next = head.getNext();
        head = next;
        return val;
    }
}