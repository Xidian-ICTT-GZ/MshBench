/*@ predicate node(Node n; Node next, int value) =
    n != null &*&
    n.val |-> value &*&
    n.nxt |-> next;
@*/

/*@ predicate stack(Stack s; list<int> values) =
    s.head |-> ?h &*&
    stack_nodes(h, values);
@*/

/*@ predicate stack_nodes(Node n; list<int> values) =
    switch (values) {
        case nil: return n == null;
        case cons(hd, tl): return
            node(n, ?next, hd) &*&
            stack_nodes(next, tl);
    };
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

    //@ requires stack(this, cons(?hd, ?tl));
    //@ ensures stack(this, tl) &*& result == hd;
    public int pop()
    {
        int val = head.val;
        Node next = head.getNext();
        head = next;
        return val;
    }
}