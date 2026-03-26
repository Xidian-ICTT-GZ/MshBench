class Node {

    int value;
    Node next;

}

/*@

predicate nodes(Node n) =
    n == null ?
        true
    :
        n.value |-> ?v &*& n.next |-> ?nx &*& nodes(nx);

@*/

class Stack {

    Node head;
    
    /*@
    predicate stack() = head |-> ?h &*& nodes(h);
    @*/
    
    //@ requires true;
    //@ ensures stack();
    Stack()
    {
        //@ close nodes(null);
        //@ close stack();
    }
    
    //@ requires stack();
    //@ ensures stack();
    void push(int element)
    {
        //@ open stack();
        Node n = new Node();
        //@ close nodes(null);
        n.value = element;
        n.next = head;
        head = n;
        //@ close nodes(n);
        //@ close stack();
    }
    
    //@ requires stack() &*& head |-> ?h &*& h != null;
    //@ ensures stack();
    int pop()
    {
        //@ open stack();
        Node h = head;
        //@ open nodes(h);
        
        int result = head.value;
        head = head.next;
        
        //@ close stack();
        return result;
    }

}

class Program {

    //@ requires true;
    //@ ensures true;
    public static void main(String[] args)
    {
        Stack s = new Stack();
        //@ open s.stack();
        //@ close s.stack();
        s.push(10);
        s.push(20);
        s.push(30);
        s.pop();
        s.pop();
        s.pop();
    }

}