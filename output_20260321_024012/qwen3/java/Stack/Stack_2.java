class Node {

    int value;
    Node next;

}

/*@ predicate node(Node n; int v, Node nx) = n.value |-> v &*& n.next |-> nx; @*/

class Stack {

    Node head;
    
    /*@ predicate stack(Stack s; list<int> elements) =
        s.head |-> ?h &*&
        nodes(h, elements);
    @*/
    
    /*@ predicate nodes(Node n; list<int> elements) =
        elements == nil ?
            n == null
        :
            n != null &*&
            node(n, ?v, ?nx) &*&
            nodes(nx, ?tail) &*&
            elements == cons(v, tail);
    @*/
    
    
    
    Stack()
        
        
    {
        //@ close stack(this, nil);
    }
    
    void push(int element)
        
        
    {
        //@ open stack(this, ?old_elements);
        Node n = new Node();
        //@ close node(n, element, head);
        n.value = element;
        n.next = head;
        head = n;
        //@ close stack(this, cons(element, old_elements));
    }
    
    int pop()
        
        
    {
        //@ open stack(this, ?elements);
        //@ assert elements == cons(?v, ?tail);
        //@ open node(head, v, ?nx);
        int result = head.value;
        head = head.next;
        //@ close stack(this, tail);
        return result;
    }

}

class Program {

    public static void main(String[] args)
        
        
    {
        //@ close stack(_, nil);
        Stack s = new Stack();
        s.push(10);
        s.push(20);
        s.push(30);
        s.pop();
        s.pop();
        s.pop();
        //@ open stack(s, _);
    }

}