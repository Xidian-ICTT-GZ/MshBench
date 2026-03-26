class Node {
    Node nxt;
    int val;

    /*@
    predicate NodeInv(Node n; Node nxt, int val) =
        n.nxt |-> nxt &*& n.val |-> val;
    @*/

    //@ requires true;
    //@ ensures NodeInv(this, n, v);
    Node(Node n, int v)
        
        
    {
        nxt = n;
        val = v;
    }

    //@ requires NodeInv(this, ?nxt, ?val);
    //@ ensures NodeInv(this, nxt, val) &*& result == nxt;
    Node getNext()
        
        
    {
        //@ open NodeInv(this, ?nxt0, ?val0);
        Node res = nxt;
        //@ close NodeInv(this, nxt0, val0);
        return res;
    }

    //@ requires NodeInv(this, ?nxt, ?val);
    //@ ensures NodeInv(this, nxt, val) &*& result == val;
    int getValue()
        
        
    {
        //@ open NodeInv(this, ?nxt0, ?val0);
        int res = val;
        //@ close NodeInv(this, nxt0, val0);
        return res;
    }
}

class Stack {
    private Node head;

    /*@
    predicate nodes(Node n) =
        n == null ?
            true
        :
            Node.NodeInv(n, ?nx, ?v) &*& nodes(nx);

    predicate StackInv(Stack s; Node h) =
        s.head |-> h &*& nodes(h);
    @*/

    //@ requires true;
    //@ ensures StackInv(this, null);
    public Stack()
        
        
    {
        head = null;
        //@ close nodes(null);
        //@ close StackInv(this, null);
        
    }

    //@ requires StackInv(this, ?h);
    //@ ensures StackInv(this, h) &*& result == (h == null);
    public boolean isEmpty()
        
        
    {
        //@ open StackInv(this, ?h0);
        boolean res = head == null;
        //@ close StackInv(this, h0);
        return res;
    }

    //@ requires StackInv(this, ?h) &*& h != null;
    //@ ensures StackInv(this, ?h2) &*& true;
    public int pop()
        
        
    {
        //@ open StackInv(this, ?h0);
        //@ open nodes(h0);
        
        
        

        //@ open Node.NodeInv(h0, ?nx0, ?v0);
        int val = head.val;
        //@ close Node.NodeInv(h0, nx0, v0);
        Node next = head.getNext();
        head = next;
        
        //@ close StackInv(this, next);
        return val;
    }
}