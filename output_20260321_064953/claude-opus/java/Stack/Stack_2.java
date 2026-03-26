class Node {

    int value;
    Node next;

    /*@
    predicate node(this) = this.value |-> _ &*& this.next |-> _; 
    @*/
}

class Stack {

    Node head;
    
    /*@
    predicate stack(this) = this.head |-> ?h &*& (h == null ? true : node(h));
    @*/
    
    Stack()
        //@ requires true;
        //@ ensures stack(this);
    {
        this.head = null;
        //@ close stack(this);
    }
    
    void push(int element)
        //@ requires stack(this);
        //@ ensures stack(this);
    {
        //@ open stack(this);
        Node n = new Node();
        //@ close node(n);
        n.value = element;
        n.next = head;
        head = n;
        //@ close stack(this);
    }
    
    int pop()
        //@ requires stack(this) &*& head != null;
        //@ ensures stack(this);
    {
        //@ open stack(this);
        int result = head.value;
        head = head.next;
        //@ close stack(this);
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