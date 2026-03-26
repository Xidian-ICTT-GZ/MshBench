/*@ predicate stack(Node head; list<int> elements) =
    head == null && elements == nil
    ||
    head != null &*&
    head->value |-> ?v &*&
    head->next |-> ?n &*&
    malloc_block_Node(head) &*&
    stack(n, ?rest) &*&
    elements == cons(v, rest);
@*/

class Node {

    int value;
    Node next;

}

class Stack {

    Node head;
    
    
    
    //@ requires true;
    //@ ensures stack(this.head, nil);
    Stack()
        
        
    {
        
    }
    
    //@ requires stack(this.head, ?elements);
    //@ ensures stack(this.head, cons(element, elements));
    void push(int element)
        
        
    {
        
        Node n = new Node();
        n.value = element;
        n.next = head;
        head = n;
        
        
    }
    
    //@ requires stack(this.head, cons(?top, ?rest));
    //@ ensures stack(this.head, rest) &*& result == top;
    int pop()
        
        
    {
        
        
        int result = head.value;
        head = head.next;
        
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