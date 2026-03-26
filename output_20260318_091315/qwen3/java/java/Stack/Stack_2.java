/*@ predicate node(Node n; int v, Node nx) =
    n != null &*&
    [1/2]n.value |-> v &*&
    [1/2]n.next |-> nx;
@*/

/*@ predicate stack(Stack s; list<int> elements) =
    s != null &*&
    s.head |-> ?h &*&
    nodes(h, elements);
@*/

/*@ predicate nodes(Node n; list<int> elements) =
    elements == nil ?
        n == null
    :
        n != null &*&
        node(n, ?v, ?nx) &*&
        nodes(nx, ?tail) &*&
        elements == cons(v, tail);
@*/

class Node {

    int value;
    Node next;

}

class Stack {

    Node head;
    
    //@ requires true;
    //@ ensures stack(this, nil);
    Stack()
    {
        
    }
    
    //@ requires stack(this, ?elements);
    //@ ensures stack(this, cons(element, elements));
    void push(int element)
    {
        Node n = new Node();
        n.value = element;
        n.next = head;
        head = n;
    }
    
    //@ requires stack(this, cons(?v, ?elements));
    //@ ensures stack(this, elements) &*& result == v;
    int pop()
    {
        int result = head.value;
        head = head.next;
        return result;
    }

}

class Program {

    //@ requires true;
    //@ ensures true;
    public static void main(String[] args)
    {
        Stack s = new Stack();
        s.push(10);
        s.push(20);
        s.push(30);
        s.pop();
        s.pop();
        s.pop();
    }

}