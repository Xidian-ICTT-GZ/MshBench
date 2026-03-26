class Node {
    Node nxt;
    int val;

    /*@
    predicate Node(Node next, int value) =
        this.nxt |-> next &*& this.val |-> value;
    @*/

    //@ requires true;
    //@ ensures Node(n, v);
    Node(Node n, int v)

    {
        nxt = n;
        val = v;
    }

    //@ requires Node(?next, ?value);
    //@ ensures Node(next, value) &*& result == next;
    Node getNext()

    {
        return nxt;
    }

    //@ requires Node(?next, ?value);
    //@ ensures Node(next, value) &*& result == value;
    int getValue()

    {
        return val;
    }
}

class Stack {
    private Node head;

    /*@
    predicate Stack(list<int> values) =
        this.head |-> ?h &*&
        (h == null ? values == nil : h.Node(?next, ?v) &*& nodes(next, ?tail) &*& values == cons(v, tail));
    
    predicate nodes(Node n, list<int> values) =
        n == null ? values == nil : n.Node(?next, ?v) &*& nodes(next, ?tail) &*& values == cons(v, tail);
    @*/

    //@ requires true;
    //@ ensures Stack(nil);
    public Stack()

    {
        head = null;

    }

    //@ requires Stack(?values);
    //@ ensures Stack(values) &*& result == (values == nil);
    public boolean isEmpty()

    {
        //@ open Stack(values);
        boolean res = head == null;
        //@ close Stack(values);
        return res;
    }

    //@ requires Stack(?values) &*& values != nil;
    //@ ensures Stack(tail(values)) &*& result == head(values);
    public int pop()

    {
        //@ open Stack(values);
        //@ open head.Node(?next, ?v);
        int val = head.val;
        //@ close head.Node(next, v);
        Node next = head.getNext();
        //@ open head.Node(next, v);
        head = next;
        //@ close Stack(tail(values));
        return val;
    }
}