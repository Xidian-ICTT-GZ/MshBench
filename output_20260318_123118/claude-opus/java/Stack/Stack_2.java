class Node {

    int value;
    Node next;

    /*@ predicate node(Node n, int v, Node nextNode) =
          n.value |-> v &*& n.next |-> nextNode;
    @*/

}

class Stack {

    Node head;

    /*@ predicate stack(Stack s, list<int> elems) =
          s.head |-> ?h &*& nodes(h, elems);
      predicate nodes(Node n, list<int> elems) =
          switch(elems) {
              case nil: n == null ? emp : false;
              case cons(headVal, tailElems):
                  n != null &*& node(n, headVal, ?nextNode) &*& nodes(nextNode, tailElems);
          };
    @*/

    //@ requires true;
    //@ ensures stack(this, nil);
    Stack()
    //@ body_invariant stack(this, nil);
    {
    }

    //@ requires stack(this, elems);
    //@ ensures stack(this, cons(element, elems));
    void push(int element)
    //@ body_invariant stack(this, ?elems);
    {
        Node n = new Node();
        //@ close node(n, element, this.head);
        n.value = element;
        n.next = head;
        head = n;
        //@ close stack(this, cons(element, elems));
    }

    //@ requires stack(this, cons(?headVal, ?tail));
    //@ ensures stack(this, tail) &*& result == headVal;
    int pop()
    //@ body_invariant stack(this, ?elems);
    {
        //@ open stack(this, elems);
        //@ open nodes(head, ?headVal, ?nextNode);
        int result = head.value;
        head = head.next;
        //@ close stack(this, tail);
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