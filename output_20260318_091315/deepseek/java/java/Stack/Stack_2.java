class Node {

    int value;
    Node next;

}

/*@
predicate Node(Node n; int v, Node nxt) =
    n.value |-> v &*& n.next |-> nxt &*& n != null;
@*/

class Stack {

    Node head;
    
    /*@
    predicate Stack() =
        head |-> ?h &*& lseg(h, null);
    
    predicate lseg(Node first, Node last) =
        first == last ?
            true
        :
            Node(first, ?v, ?nxt) &*& lseg(nxt, last);
    @*/
    
    Stack()
        //@ requires true;
        //@ ensures Stack();
    {
        //@ close Stack();
    }
    
    void push(int element)
        //@ requires Stack();
        //@ ensures Stack();
    {
        //@ open Stack();
        Node n = new Node();
        n.value = element;
        //@ close Node(n, element, head);
        n.next = head;
        head = n;
        //@ close lseg(head, null);
        //@ close Stack();
    }
    
    int pop()
        //@ requires Stack() &*& head != null;
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