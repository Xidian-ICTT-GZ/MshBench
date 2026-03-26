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

predicate stack(Stack s) = s.head |-> ?h &*& nodes(h);
@*/

class Stack {

    Node head;
    
    
    
    Stack()
        
        
    //@ requires true;
    //@ ensures stack(this);
    {
        //@ close nodes(null);
        //@ close stack(this);
    }
    
    void push(int element)
        
        
    //@ requires stack(this);
    //@ ensures stack(this);
    {
        //@ open stack(this);
        
        Node n = new Node();
        n.value = element;
        n.next = head;
        head = n;
        
        //@ close nodes(n);
        //@ close stack(this);
        
    }
    
    int pop()
        
        
    //@ requires stack(this) &*& head != null;
    //@ ensures stack(this);
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