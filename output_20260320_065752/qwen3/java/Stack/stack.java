class Node {
    Node nxt;
    int val;

    /*@
    predicate node(Node n; Node next, int value) =
        n != null &*& n.val |-> value &*& n.nxt |-> next;
    @*/

    //@ requires true;
    //@ ensures node(this, n, v);
    Node(Node n, int v)
        
        
    {
        nxt = n;
        val = v;
    }

    //@ requires node(this, ?next, ?value);
    //@ ensures node(this, next, value) &*& result == next;
    Node getNext()
        
        
    {
        return nxt;
    }

    //@ requires node(this, ?next, ?value);
    //@ ensures node(this, next, value) &*& result == value;
    int getValue()
        
        
    {
        return val;
    }
}

class Stack {
    private Node head;

    /*@
    predicate stack(Stack s; list<int> values) =
        s != null &*& s.head |-> ?h &*&
        switch (values) {
            case nil: return h == null;
            case cons(v, vs): return node(h, ?n, v) &*& stack_nodes(n, vs);
        };
    
    predicate stack_nodes(Node n; list<int> values) =
        switch (values) {
            case nil: return n == null;
            case cons(v, vs): return node(n, ?m, v) &*& stack_nodes(m, vs);
        };
    @*/

    //@ requires true;
    //@ ensures stack(this, nil);
    public Stack()
        
        
    {
        head = null;
        
    }

    //@ requires stack(this, ?values);
    //@ ensures stack(this, values) &*& result == (values == nil);
    public boolean isEmpty()
        
        
    {
        return head == null;
    }

    //@ requires stack(this, cons(?v, ?vs));
    //@ ensures stack(this, vs) &*& result == v;
    public int pop()
        
        
    {
        
        
        

        //@ open stack(this, cons(v, vs));
        //@ open node(head, ?next, v);
        int val = head.val;
        Node next = head.getNext();
        head = next;
        //@ close stack(this, vs);
        
        return val;
    }
}