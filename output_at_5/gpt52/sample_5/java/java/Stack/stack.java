class Node {
    Node nxt;
    int val;

    /*@
    predicate NodeInv() =
        this.nxt |-> ?nxt0 &*& this.val |-> ?val0;
    @*/

    //@ requires true;
    //@ ensures NodeInv();
    Node(Node n, int v)
        
        
    {
        nxt = n;
        val = v;
        //@ close NodeInv();
    }

    //@ requires NodeInv();
    //@ ensures NodeInv();
    Node getNext()
        
        
    {
        //@ open NodeInv();
        Node r = nxt;
        //@ close NodeInv();
        return r;
    }

    //@ requires NodeInv();
    //@ ensures NodeInv();
    int getValue()
        
        
    {
        //@ open NodeInv();
        int r = val;
        //@ close NodeInv();
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
            n.NodeInv() &*& nodes(n.nxt);

    predicate StackInv() =
        this.head |-> ?h &*& nodes(h);
    @*/

    //@ requires true;
    //@ ensures StackInv();
    public Stack()
        
        
    {
        head = null;
        //@ close nodes(null);
        //@ close StackInv();
        
    }

    //@ requires StackInv();
    //@ ensures StackInv();
    public boolean isEmpty()
        
        
    {
        //@ open StackInv();
        boolean r = head == null;
        //@ close StackInv();
        return r;
    }

    //@ requires StackInv();
    //@ ensures StackInv();
    public int pop()
        
        
    {
        //@ open StackInv();
        //@ open nodes(head);
        //@ open head.NodeInv();
        
        
        

        int val = head.val;
        Node next = head.getNext();
        head = next;
        
        //@ close nodes(next);
        //@ close StackInv();
        return val;
    }
}