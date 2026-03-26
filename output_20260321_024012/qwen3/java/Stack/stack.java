class Node {
    Node nxt;
    int val;

    /*@
    predicate node(int v; Node n) = val |-> v &*& nxt |-> n;
    @*/

    //@ requires true;
    //@ ensures node(v, n);
    Node(Node n, int v)
        
        
    {
        nxt = n;
        val = v;
    }

    //@ requires node(?v, ?n);
    //@ ensures node(v, n) &*& result == n;
    Node getNext()
        
        
    {
        return nxt;
    }

    //@ requires node(?v, ?n);
    //@ ensures node(v, n) &*& result == v;
    int getValue()
        
        
    {
        return val;
    }
}

class Stack {
    private Node head;

    /*@
    predicate stack() = head |-> ?h &*& (h == null ? true : node(?v, ?n));
    @*/

    //@ requires true;
    //@ ensures stack();
    public Stack()
        
        
    {
        head = null;
        
    }

    //@ requires stack();
    //@ ensures stack() &*& result == (head == null);
    public boolean isEmpty()
        
        
    {
        return head == null;
    }

    //@ requires stack() &*& head != null;
    //@ ensures stack();
    public int pop()
        
        
    {
        
        
        

        //@ open stack();
        //@ open node(?v, ?n);
        int val = head.val;
        Node next = head.getNext();
        head = next;
        //@ close stack();
        
        return val;
    }
}