class Node {

    int value;
    Node next;

    /*@
    predicate node() = this.value |-> _ &*& this.next |-> _;
    @*/
}

class Stack {

    Node head;

    /*@
    predicate stack() = head == null ? true : head.node() &*& true;
    @*/
    
    Stack()
        //@ requires true;
        //@ ensures stack();
    {
        head = null;
    }
    
    void push(int element)
        //@ requires stack();
        //@ ensures stack();
    {
        //@ open stack();
        Node n = new Node();
        //@ n.value = element; // field write allowed since n is fresh
        n.value = element;
        n.next = head;
        head = n;
        //@ close stack();
    }
    
    int pop()
        //@ requires stack() &*& head != null;
        //@ ensures stack();
    {
        //@ open stack();
        int result = head.value;
        head = head.next;
        //@ close stack();
        return result;
    }

}

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
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