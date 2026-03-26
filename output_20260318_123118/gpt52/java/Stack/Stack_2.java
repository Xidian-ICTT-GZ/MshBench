class Node {

    int value;
    Node next;

}

/*@

predicate nodes(Node n) =
    n == null ?
        emp
    :
        n.value |-> ?v &*& n.next |-> ?nx &*& nodes(nx);

predicate stack(Stack s) =
    s.head |-> ?h &*& nodes(h);

@*/

class Stack {

    Node head;
    
    
    
    //@ requires emp;
    //@ ensures stack(this);
    Stack()
        
        
    {
        
    }
    
    //@ requires stack(this);
    //@ ensures stack(this);
    void push(int element)
        
        
    {
        
        Node n = new Node();
        n.value = element;
        n.next = head;
        head = n;
        
        
    }
    
    //@ requires stack(this) &*& this.head |-> ?h &*& h != null;
    //@ ensures stack(this);
    int pop()
        
        
    {
        
        
        int result = head.value;
        head = head.next;
        
        return result;
    }

}

class Program {

    //@ requires emp;
    //@ ensures emp;
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