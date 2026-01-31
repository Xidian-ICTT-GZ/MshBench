class Node {
    Node nxt;
    int val;

    Node(Node n, int v)
        //@ requires true;
        //@ ensures this.nxt |-> n &*& this.val |-> v;
    {
        nxt = n;
        val = v;
    }

    Node getNext()
        //@ requires this.nxt |-> ?n;
        //@ ensures this.nxt |-> n &*& result == n;
    {
        return nxt;
    }

    int getValue()
        //@ requires this.val |-> ?v;
        //@ ensures this.val |-> v &*& result == v;
    {
        return val;
    }
}
/*@
predicate NodeInv(Node t; Node n, int v) =
    t.nxt |-> n &*& t.val |-> v;

predicate List(Node n;) =
    n == null ?
        emp
    :
        NodeInv(n, ?nn, _) &*& List(nn);

predicate StackInv(Stack t;) =
    t.head |-> ?h &*& List(h);

predicate NonEmptyStackInv(Stack t;) =
    t.head |-> ?h &*& h != null &*& List(h);
@*/

class Stack {
    private Node head;

    public Stack()
        //@ requires true;
        //@ ensures StackInv(this);
    {
        head = null;
        //@ close StackInv(this);
    }

    public boolean isEmpty()
        //@ requires StackInv(this);
        //@ ensures result ? StackInv(this) : NonEmptyStackInv(this);
    {
        return head == null;
    }

    public int pop()
        //@ requires NonEmptyStackInv(this);
        //@ ensures StackInv(this);
    {
        //@ open NonEmptyStackInv(this);
        //@ open List(head);
        //@ open NodeInv(head, ?nxt, ?v);

        int val = head.val;
        Node next = head.getNext();
        head = next;
        //@ close StackInv(this);
        return val;
    }
}
