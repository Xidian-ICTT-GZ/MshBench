class Node {
    int value;
    Node next;
}

/*@
predicate node(Node n, int v, Node next) = n != null &*& n.value |-> v &*& n.next |-> next;

fixpoint<int> head(list<int> xs) {
    switch(xs) {
        case nil: return 0; // dummy, never called on nil
        case cons(x, _): return x;
    }
}

predicate nodes(Node n, list<int> xs) =
    n == null ? xs == nil :
        node(n, head(xs), ?next) &*& nodes(next, xs.tail);

predicate stack(Stack this, list<int> xs) =
    this.head |-> ?h &*& nodes(h, xs);
@*/

class Stack {
    Node head;
    
    /*@
    requires true;
    ensures stack(this, nil);
    @*/
    Stack() {
        head = null;
    }
    
    /*@
    requires stack(this, ?xs);
    ensures stack(this, cons(element, xs));
    @*/
    void push(int element) {
        //@ open stack(this, xs);
        Node n = new Node();
        n.value = element;
        n.next = head;
        head = n;
        //@ close node(n, element, head.next);
        //@ close stack(this, cons(element, xs));
    }
    
    /*@
    requires stack(this, ?xs) &*& xs != nil;
    ensures stack(this, xs.tail) &*& result == head(xs);
    @*/
    int pop() {
        //@ open stack(this, xs);
        int result = head.value;
        head = head.next;
        //@ close stack(this, xs.tail);
        return result;
    }
}

class Program {
    public static void main(String[] args) {
        Stack s = new Stack();
        s.push(10);
        s.push(20);
        s.push(30);
        s.pop();
        s.pop();
        s.pop();
    }
}