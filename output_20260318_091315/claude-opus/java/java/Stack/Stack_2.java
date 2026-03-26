class Node {
    int value;
    Node next;

    /*@ 
    predicate nodes(Node n, list<int> vs) = 
        n == null ?
            emp
        :
            n.value |-> ?v &*& n.next |-> ?nx &*& nodes(nx, ?nvs) &*& vs == cons(v, nvs);
    @*/
}

class Stack {
    Node head;

    /*@ 
    predicate stack(Stack s, list<int> vs) = 
        s.head |-> ?h &*& nodes(h, vs);
    @*/

    //@ requires stack(this, ?vs);
    //@ ensures stack(this, cons(element, vs));
    void push(int element)
    {
        Node n = new Node();
        n.value = element;
        n.next = head;
        head = n;
    }

    //@ requires stack(this, ?vs) &*& vs != nil;
    //@ ensures stack(this, tail(vs)) &*& result == head.value;
    int pop()
    {
        int result = head.value;
        head = head.next;

        return result;
    }

    //@ requires emp;
    //@ ensures stack(this, nil);
    Stack()
    {
    }
}

class Program {
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