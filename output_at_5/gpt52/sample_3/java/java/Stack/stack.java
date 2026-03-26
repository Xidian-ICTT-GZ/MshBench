class Node {
    Node nxt;
    int val;

    /*@
    predicate NodeInv(Node n; Node nxt, int val) =
        n.nxt |-> nxt &*& n.val |-> val;
    @*/

    //@ requires true;
    //@ ensures NodeInv(this; n, v);
    Node(Node n, int v)
        
        
    {
        nxt = n;
        val = v;
        //@ close NodeInv(this; n, v);
    }

    //@ requires NodeInv(this; ?nxt0, ?val0);
    //@ ensures NodeInv(this; nxt0, val0) &*& result == nxt0;
    Node getNext()
        
        
    {
        //@ open NodeInv(this; nxt0, val0);
        Node r = nxt;
        //@ close NodeInv(this; nxt0, val0);
        return r;
    }

    //@ requires NodeInv(this; ?nxt0, ?val0);
    //@ ensures NodeInv(this; nxt0, val0) &*& result == val0;
    int getValue()
        
        
    {
        //@ open NodeInv(this; nxt0, val0);
        int r = val;
        //@ close NodeInv(this; nxt0, val0);
        return r;
    }
}

class Stack {
    private Node head;

    /*@
    predicate nodes(Node n) =
        n == null ?
            true
        :
            NodeInv(n; ?nxt, ?v) &*& nodes(nxt);

    predicate StackInv(Stack s; Node h) =
        s.head |-> h &*& nodes(h);
    @*/

    //@ requires true;
    //@ ensures StackInv(this; null);
    public Stack()
        
        
    {
        head = null;
        //@ close nodes(null);
        //@ close StackInv(this; null);
        
    }

    //@ requires StackInv(this; ?h);
    //@ ensures StackInv(this; h) &*& result == (h == null);
    public boolean isEmpty()
        
        
    {
        //@ open StackInv(this; h);
        boolean r = head == null;
        //@ close StackInv(this; h);
        return r;
    }

    //@ requires StackInv(this; ?h) &*& h != null;
    //@ ensures StackInv(this; ?h2) &*& nodes(h);
    public int pop()
        
        
    {
        //@ open StackInv(this; h);
        //@ open nodes(h);
        //@ open NodeInv(h; ?nxt, ?v);
        
        
        

        int val = head.val;
        Node next = head.getNext();
        head = next;
        
        //@ close NodeInv(h; nxt, v);
        //@ close nodes(h);
        //@ close StackInv(this; next);
        return val;
    }
}