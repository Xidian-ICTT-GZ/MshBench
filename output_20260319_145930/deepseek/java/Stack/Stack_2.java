class Node {

    int value;
    Node next;

    //@ predicate Node() = value |-> _ &*& next |-> _;

    Node()
    //@ requires true;
    //@ ensures Node();
    {
        //@ close Node();
    }

}

class Stack {

    Node head;

    /*@
    predicate Stack() =
        head |-> ?h &*& h == null ? true : h.Node() &*& h.next |-> ?n &*& n.Stack();
    @*/

    Stack()
    //@ requires true;
    //@ ensures Stack();
    {
        head = null;
        //@ close Stack();
    }

    void push(int element)
    //@ requires Stack();
    //@ ensures Stack();
    {
        //@ open Stack();
        Node n = new Node();
        n.value = element;
        n.next = head;
        head = n;
        //@ close Node();
        //@ close Stack();
    }

    int pop()
    //@ requires Stack() &*& head != null;
    //@ ensures Stack();
    {
        //@ open Stack();
        int result = head.value;
        head = head.next;
        //@ close Stack();
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