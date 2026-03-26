/*@ predicate node(Node n; Node next, int value) =
    n != null &*& n.nxt |-> next &*& n.val |-> value;
@*/

class Node {
    Node nxt;
    int val;

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

/*@ predicate stack(Stack s; list<int> values) =
    s.head |-> ?h &*&
    (h == null ?
        values == nil
    :
        node(h, ?next, ?v) &*& stack_nodes(next, tail(values)) &*& values == cons(v, tail(values))
    );
@*/

/*@ predicate stack_nodes(Node n; list<int> values) =
    n == null ?
        values == nil
    :
        node(n, ?next, ?v) &*& stack_nodes(next, tail(values)) &*& values == cons(v, tail(values));
@*/

class Stack {
    private Node head;

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

    //@ requires stack(this, ?values) &*& values != nil;
    //@ ensures stack(this, tail(values)) &*& result == head(values);
    public int pop()
    {
        //@ open stack(this, values);
        int val = head.val;
        Node next = head.getNext();
        head = next;
        //@ close stack(this, tail(values));
        return val;
    }
}