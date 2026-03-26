class Node {

    int value;
    Node next;

}

/*@
predicate Node(Node n; int v, Node nxt) =
    n.value |-> v &*& n.next |-> nxt;
@*/

class Stack {

    Node head;
    
    /*@
    predicate Stack(Node h) =
        h == null ?
            emp
        :
            Node(h, ?v, ?nxt) &*& Stack(nxt);
    @*/
    
    
    Stack()
        //@ requires true;
        //@ ensures Stack(head);
    {
        //@ close Stack(null);
    }
    
    void push(int element)
        //@ requires Stack(head);
        //@ ensures Stack(head);
    {
        Node n = new Node();
        n.value = element;
        //@ close Node(n, element, head);
        n.next = head;
        head = n;
        //@ open Stack(head.next);
        //@ close Stack(head);
    }
    
    int pop()
        //@ requires Stack(head) &*& head != null;
        //@ ensures Stack(head);
    {
        //@ open Stack(head);
        int result = head.value;
        Node next = head.next;
        head = next;
        //@ close Stack(head);
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