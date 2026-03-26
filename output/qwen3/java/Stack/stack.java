class Node {
    Node nxt;
    int val;

    //@ requires true;
    //@ ensures this.nxt == n &*& this.val == v;
    Node(Node n, int v) {
        nxt = n        val = v;
    }

    //@ requires true;
    //@ ensures result == this.nxt;
    Node getNext() {
        return nxt;
    }

    //@ requires true;
    //@ ensures result == this.val;
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
    //@ ensures head == null;
    public Stack() {
        head = null;
    }

    //@ requires true;
    //@ ensures result == (head == null);
    public boolean isEmpty() {
        return head == null;
    }

    //@ requires head != null &*& node(head; ?v, ?next);
    //@ ensures result == v &*& head == next;
    public int pop() {
        int val = head.val;
        Node next = head.getNext();
        head = next;
        return val;
    }
}