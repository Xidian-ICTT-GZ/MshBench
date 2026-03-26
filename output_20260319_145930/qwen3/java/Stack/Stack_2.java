/*@ 
predicate Nodes(Node n;) =
    n == null ?
        true
    :
        n |-> { value, next } &*& Nodes(n.next;);
@*/

class Node {

    int value;
    Node next;

}

class Stack {

    Node head;
    
    //@ predicate Stack(Stack s;) = s.head |-> ?h &*& Nodes(h;);
    
    Stack()
    //@ requires true;
    //@ ensures Stack(this;);
    {
        //@ close Stack(this;);
    }
    
    void push(int element)
    //@ requires Stack(this;);
    //@ ensures Stack(this;);
    {
        //@ open Stack(this;);
        Node n = new Node();
        n.value = element;
        n.next = head;
        head = n;
        //@ close Stack(this;);
    }
    
    int pop()
    //@ requires Stack(this;) &*& this.head != null;
    //@ ensures Stack(this;) &*& result == old_val(head).value;
    {
        //@ open Stack(this;);
        //@ assert head != null;
        int result = head.value;
        head = head.next;
        //@ close Stack(this;);
        return result;
    }

}

class Program {

    public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    {
        Stack s = new Stack();
        //@ close Stack(s;);
        s.push(10);
        s.push(20);
        s.push(30);
        s.pop();
        s.pop();
        s.pop();
        //@ open Stack(s;);
    }

}