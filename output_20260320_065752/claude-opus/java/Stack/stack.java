class Node {
    Node nxt;
    int val;

/*@
predicate node(self, Node nxt, int val) = this == self &*& this.nxt |-> nxt &*& this.val |-> val;
@*/

    Node(Node n, int v)
        //@ requires true;
        //@ ensures node(this, n, v);
    {
        nxt = n;
        val = v;
    }

    Node getNext()
        //@ requires node(this, ?n, ?v);
        //@ ensures node(this, n, v) &*& result == n;
    {
        return nxt;
    }

    int getValue()
        //@ requires node(this, ?n, ?v);
        //@ ensures node(this, n, v) &*& result == v;
    {
        return val;
    }
}

class Stack {
    private Node head;

/*@
predicate stack(Stack s, Node head) = s.head |-> head &*& (head == null ? true : node(head, ?n, ?v));
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
        //@ requires stack(this, ?h) &*& h != null &*& node(h, ?n, ?v);
        //@ ensures stack(this, n) &*& result == v;
    {
        //@ open node(h, n, v);
        int val = head.val;
        Node next = head.getNext();
        head = next;
        //@ close stack(this, next);
        return val;
    }
}