class Node {
    Node nxt;
    int val;

    /*@
    predicate NodeInv(Node n; Node nxt, int val) =
        n.nxt |-> nxt &*& n.val |-> val;
    @*/

    Node(Node n, int v)
        //@ requires true;
        //@ ensures NodeInv(this, n, v);
        
    {
        nxt = n;
        val = v;
        //@ close NodeInv(this, n, v);
    }

    Node getNext()
        //@ requires NodeInv(this, ?nxt, ?val);
        //@ ensures NodeInv(this, nxt, val) &*& result == nxt;
        
    {
        //@ open NodeInv(this, ?nxt0, ?val0);
        Node res = nxt;
        //@ close NodeInv(this, nxt0, val0);
        return res;
    }

    int getValue()
        //@ requires NodeInv(this, ?nxt, ?val);
        //@ ensures NodeInv(this, nxt, val) &*& result == val;
        
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
            NodeInv(n, ?nxt, ?val) &*& nodes(nxt);

    predicate StackInv(Stack s; Node h) =
        s.head |-> h &*& nodes(h);
    @*/

    public Stack()
        //@ requires true;
        //@ ensures StackInv(this, null);
        
    {
        head = null;
        //@ close nodes(null);
        //@ close StackInv(this, null);
        
    }

    public boolean isEmpty()
        //@ requires StackInv(this, ?h);
        //@ ensures StackInv(this, h) &*& result == (h == null);
        
    {
        //@ open StackInv(this, h);
        boolean res = head == null;
        //@ close StackInv(this, h);
        return res;
    }

    public int pop()
        //@ requires StackInv(this, ?h) &*& h != null;
        //@ ensures StackInv(this, ?h2);
        
    {
        //@ open StackInv(this, h);
        //@ open nodes(h);
        //@ open NodeInv(h, ?nxt, ?v);
        
        
        

        int val = head.val;
        //@ close NodeInv(h, nxt, v);
        Node next = head.getNext();
        head = next;
        //@ close nodes(next);
        //@ close StackInv(this, next);
        
        return val;
    }
}