class Node {
    Node nxt;
    int val;

    //@ predicate valid() = this.nxt |-> ?n &*& this.val |-> ?v;
    //@ requires true;
    //@ ensures valid();
    Node(Node n, int v)
    {
        nxt = n;
        val = v;
    }

    //@ requires valid();
    //@ ensures valid() &*& result == nxt;
    Node getNext()
    {
        return nxt;
    }

    //@ requires valid();
    //@ ensures valid() &*& result == val;
    int getValue()
    {
        return val;
    }
}

class Stack {
    private Node head;

    //@ predicate valid() = head |-> null;
    //@ requires true;
    //@ ensures valid();
    public Stack()
    {
        head = null;
    }

    //@ requires valid();
    //@ ensures valid() &*& result == (head == null);
    public boolean isEmpty()
    {
        return head == null;
    }

    //@ requires valid() &*& head != null;
    //@ ensures valid();
    public int pop()
    {
        //@ open valid();
        //@ open Node.valid(head);
        int val = head.val;
        Node next = head.getNext();
        head = next;
        //@ close valid();
        return val;
    }
}