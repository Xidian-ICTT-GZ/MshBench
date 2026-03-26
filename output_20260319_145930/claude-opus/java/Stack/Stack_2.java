/*@
predicate nodes(Node n;) =
    n == null ? true : n.value |-> _ &*& n.next |-> ?next &*& nodes(next);

predicate Stack(Stack s;) =
    s.head |-> ?head &*& nodes(head);
@*/

class Node {

    int value;
    Node next;

}

class Stack {

    Node head;
    
    Stack()
        //@ requires true;
        //@ ensures Stack(this);
    {
        //@ close nodes(null);
        //@ close Stack(this);
    }
    
    void push(int element)
        //@ requires Stack(this);
        //@ ensures Stack(this);
    {
        //@ open Stack(this);
        Node n = new Node();
        n.value = element;
        n.next = head;
        head = n;
        //@ close nodes(n);
        //@ close Stack(this);
    }
    
    int pop()
        //@ requires Stack(this) &*& this.head |-> ?h &*& h != null;
        //@ ensures Stack(this);
    {
        //@ open Stack(this);
        //@ open nodes(head);
        int result = head.value;
        head = head.next;
        //@ close Stack(this);
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
        //@ open Stack(s);
        //@ open nodes(s.head);
        s.pop();
        //@ open Stack(s);
        //@ open nodes(s.head);
        s.pop();
        //@ open Stack(s);
        //@ open nodes(s.head);
        s.pop();
    }

}