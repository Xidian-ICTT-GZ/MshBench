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

predicate stack(Stack s) =
    s.head |-> ?h &*& nodes(h);
@*/

class Stack {

    Node head;
    
    
    
    //@ requires true;
    //@ ensures stack(this);
    Stack()
        
        
    {
        //@ close nodes(null);
        //@ close stack(this);
    }
    
    //@ requires stack(this);
    //@ ensures stack(this);
    void push(int element)
        
        
    {
        //@ open stack(this);
        Node n = new Node();
        n.value = element;
        n.next = head;
        //@ close nodes(n);
        head = n;
        //@ close stack(this);
        
        
    }
    
    //@ requires stack(this) &*& this.head != null;
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