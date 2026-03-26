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
    
    //@ predicate Stack() = head |-> ?h &*& lseg(h, null);
    
    //@ predicate lseg(Node n, Node end) = n == end ? true : n.Node() &*& n.next |-> ?next &*& lseg(next, end);
    
    
    
    Stack()
    //@ requires true;
    //@ ensures Stack();
        
    {
        //@ close lseg(null, null);
        //@ close Stack();
    }
    
    void push(int element)
    //@ requires Stack();
    //@ ensures Stack();
        
    {
        //@ open Stack();
        Node n = new Node();
        n.value = element;
        //@ open lseg(head, null);
        n.next = head;
        //@ close lseg(n, null);
        head = n;
        //@ close Stack();
        
    }
    
    int pop()
    //@ requires Stack();
    //@ ensures Stack();
        
    {
        //@ open Stack();
        //@ open lseg(head, null);
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