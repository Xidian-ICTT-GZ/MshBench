class Node {
    Node nxt;
    int val;

    /*@
    predicate node(Node n, Node next, int v) =
        n.nxt |-> next &*& n.val |-> v;
    @*/

    //@ requires this.nxt |-> n &*& this.val |-> v;
    //@ ensures node(this, n, v);
    Node(Node n, int v)
        
        
    {
        nxt = n;
        val = v;
    }

    //@ requires node(this, ?next, ?v);
    //@ ensures node(this, next, v) &*& result == next;
    Node getNext()
        
        
    {
        //@ open node(this, next, v);
        Node r = nxt;
        //@ close node(this, next, v);
        return r;
    }

    //@ requires node(this, ?next, ?v);
    //@ ensures node(this, next, v) &*& result == v;
    int getValue()
        
        
    {
        //@ open node(this, next, v);
        int r = val;
        //@ close node(this, next, v);
        return r;
    }
}

class Stack {
    private Node head;

    /*@
    predicate stack(Stack s; Node h) =
        s.head |-> h;
    @*/

    //@ requires stack(this, ?h);
    //@ ensures stack(this, null);
    public Stack()
        
        
    {
        //@ open stack(this, h);
        head = null;
        //@ close stack(this, null);
        
    }

    //@ requires stack(this, ?h);
    //@ ensures stack(this, h) &*& result == (h == null);
    public boolean isEmpty()
        
        
    {
        //@ open stack(this, h);
        boolean r = head == null;
        //@ close stack(this, h);
        return r;
    }

    //@ requires stack(this, ?h) &*& h != null &*& Node.node(h, ?n, ?v);
    //@ ensures stack(this, n) &*& result == v;
    public int pop()
        
        
    {
        //@ open stack(this, h);
        //@ open Node.node(h, n, v);
        
        
        

        int val = head.val;
        Node next = head.getNext();
        head = next;
        
        //@ close stack(this, next);
        return val;
    }
}