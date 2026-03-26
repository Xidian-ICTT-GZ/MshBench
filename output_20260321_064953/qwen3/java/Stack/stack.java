class Node {
    Node nxt;
    int val;

    /*@
    predicate node(Node n; Node next, int value) =
        n != null &*& n.nxt |-> next &*& n.val |-> value;
    @*/

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

    /*@
    predicate stack(Stack s; list<int> values) =
        s != null &*& s.head |-> ?h &*&
        (h == null ?
            values == nil
        :
            node(h, ?next, ?v) &*& stack_values(h, values));
    
    fixpoint list<int> stack_values(Node h; list<int> vs) {
        switch (vs) {
            case nil: return nil;
            case cons(v, rest): return cons(v, stack_values_rest(h, v, rest));
        }
    }

    fixpoint list<int> stack_values_rest(Node h, int v, list<int> rest) {
        return stack_values(h.nxt, rest);
    }
    @*/

    //@ requires true;
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

    //@ requires stack(this, cons(?v, ?rest));
    //@ ensures stack(this, rest) &*& result == v;
    public int pop()
        
        
    {
        
        
        

        //@ open stack(this, _);
        //@ open node(head, ?next, ?val);
        int val = head.val;
        Node next = head.getNext();
        head = next;
        //@ close stack(this, rest);
        
        return val;
    }
}