class Node {

    int value;
    Node next;

}

/*@ predicate node(Node n; int v, Node nxt) = n.value |-> v &*& n.next |-> nxt; @*/

class Stack {

    Node head;
    
    /*@ predicate stack(Stack s; list<int> elements) =
        s.head |-> ?h &*&
        switch (elements) {
            case nil: return h == null;
            case cons(hd, tl): return h != null &*& node(h, hd, ?next) &*& stack(?s2, tl) &*& s2.head |-> next;
        };
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
        //@ assert elements == cons(?hd, ?tl);
        int result = head.value;
        //@ open node(head, hd, ?next);
        head = head.next;
        //@ close stack(this, tl);
        return result;
    }

}

class Program {

    public static void main(String[] args)
        
        
    {
        Stack s = new Stack();
        //@ close stack(s, nil);
        s.push(10);
        //@ open stack(s, _); close stack(s, cons(10, nil));
        s.push(20);
        //@ open stack(s, _); close stack(s, cons(20, cons(10, nil)));
        s.push(30);
        //@ open stack(s, _); close stack(s, cons(30, cons(20, cons(10, nil))));
        s.pop();
        //@ open stack(s, _); close stack(s, cons(20, cons(10, nil)));
        s.pop();
        //@ open stack(s, _); close stack(s, cons(10, nil));
        s.pop();
        //@ open stack(s, _); close stack(s, nil);
    }

}