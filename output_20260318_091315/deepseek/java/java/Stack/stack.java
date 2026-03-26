class Node {
    Node nxt;
    int val;

    //@ predicate valid() = this.nxt |-> ?n &*& this.val |-> ?v;
    //@ predicate valid_list() = valid() &*& (n == null ? true : n.valid_list());

    Node(Node n, int v)
    //@ requires true;
    //@ ensures valid() &*& this.nxt |-> n &*& this.val |-> v;
    {
        nxt = n;
        val = v;
    }

    Node getNext()
    //@ requires valid();
    //@ ensures valid() &*& result == this.nxt;
    {
        return nxt;
    }

    int getValue()
    //@ requires valid();
    //@ ensures valid() &*& result == this.val;
    {
        return val;
    }
}

class Stack {
    private Node head;

    //@ predicate valid() = head |-> ?h &*& (h == null ? true : h.valid_list());

    public Stack()
    //@ requires true;
    //@ ensures valid() &*& head |-> null;
    {
        head = null;
    }

    public boolean isEmpty()
    //@ requires valid();
    //@ ensures valid() &*& result == (head == null);
    {
        return head == null;
    }

    public int pop()
    //@ requires valid() &*& head != null;
    //@ ensures valid();
    {
        int val = head.val;
        Node next = head.getNext();
        head = next;
        return val;
    }
}