class Node {
    Node nxt;
    int val;

    /*@
    predicate node(Node n, int v) = n != null && n.val == v &*& (n.nxt == null || node(n.nxt));
    @*/

    Node(Node n, int v)
        //@ requires true;
        //@ ensures this == new Node(n, v);
    {
        nxt = n;
        val = v;
    }

    Node getNext()
        //@ requires this != null;
        //@ ensures result == nxt;
    {
        return nxt;
    }

    int getValue()
        //@ requires this != null;
        //@ ensures result == val;
    {
        return val;
    }
}

class Stack {
    private Node head;

    /*@
    predicate stack(Stack s) = s.head == null || node(s.head);
    @*/

    public Stack()
        //@ requires true;
        //@ ensures stack(this);
    {
        head = null;
        
    }

    public boolean isEmpty()
        //@ requires stack(this);
        //@ ensures result == (head == null);
    {
        return head == null;
    }

    public int pop()
        //@ requires stack(this) &*& head != null;
        //@ ensures stack(this) &*& result == head.val;
    {
        int val = head.val;
        Node next = head.getNext();
        head = next;
        
        return val;
    }
}