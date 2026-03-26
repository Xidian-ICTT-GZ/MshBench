/*@
predicate nodes(Node n) =
    n == null ?
        true
    :
        n.value |-> _ &*& n.next |-> ?next &*& nodes(next);
predicate stack(Stack s) =
    s.head |-> ?h &*& nodes(h);
@*/
class Node {

    int value;
    Node next;

}

class Stack {

    Node head;
    
    //@ requires true;
    //@ ensures stack(this);
    Stack()
    {
        //@ head = null;
    }
    
    //@ requires stack(this);
    //@ ensures stack(this);
    void push(int element)
    {
        //@ open stack(this);
        Node n = new Node();
        n.value = element;
        n.next = head;
        head = n;
        //@ close stack(this);
    }
    
    //@ requires stack(this) &*& head != null;
    //@ ensures stack(this);
    int pop()
    {
        //@ open stack(this);
        //@ open nodes(head);
        int result = head.value;
        head = head.next;
        //@ close stack(this);
        return result;
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