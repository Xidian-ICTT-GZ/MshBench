class Node {
    Node nxt;
    int val;

    /*@
    predicate NodeInv(Node n) =
        n.nxt |-> ?nxt0 &*& n.val |-> ?val0;
    @*/

    //@ requires true;
    //@ ensures NodeInv(this);
    Node(Node n, int v)
        
        
    {
        nxt = n;
        val = v;
        //@ close NodeInv(this);
    }

    //@ requires NodeInv(this);
    //@ ensures NodeInv(this) &*& result == ?r;
    Node getNext()
        
        
    {
        //@ open NodeInv(this);
        Node r = nxt;
        //@ close NodeInv(this);
        return r;
    }

    //@ requires NodeInv(this);
    //@ ensures NodeInv(this) &*& result == ?r;
    int getValue()
        
        
    {
        //@ open NodeInv(this);
        int r = val;
        //@ close NodeInv(this);
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
            NodeInv(n) &*& nodes(n.nxt);

    predicate StackInv(Stack s) =
        s.head |-> ?h &*& nodes(h);
    @*/

    //@ requires true;
    //@ ensures StackInv(this);
    public Stack()
        
        
    {
        head = null;
        //@ close nodes(null);
        //@ close StackInv(this);
        
    }

    //@ requires StackInv(this);
    //@ ensures StackInv(this);
    public boolean isEmpty()
        
        
    {
        //@ open StackInv(this);
        boolean r = head == null;
        //@ close StackInv(this);
        return r;
    }

    //@ requires StackInv(this) &*& head != null;
    //@ ensures StackInv(this);
    public int pop()
        
        
    {
        //@ open StackInv(this);
        //@ assert head |-> ?h &*& nodes(h);
        //@ open nodes(h);
        //@ open NodeInv(h);
        
        
        

        int val = head.val;
        Node next = head.getNext();
        head = next;
        
        //@ close NodeInv(h);
        //@ close nodes(h);
        //@ close StackInv(this);
        return val;
    }
}