class Node {
    Node nxt;
    int val;

    /*@ predicate valid(int v, Node nx) = this.val |-> v &*& this.nxt |-> nx; @*/

    /*@
      requires true;
      ensures valid(v, n);
    @*/
    Node(Node n, int v)
    {
        nxt = n;
        val = v;
    }

    /*@
      requires valid(?v, ?nx);
      ensures valid(v, nx) &*& result == nx;
    @*/
    Node getNext()
    {
        return nxt;
    }

    /*@
      requires valid(?v, ?nx);
      ensures valid(v, nx) &*& result == v;
    @*/
    int getValue()
    {
        return val;
    }
}

/*@ predicate StackList(Node n, int count) =
      (n == null &*& count == 0) ||
      (n != null &*& count > 0 &*& n |-> Node.valid(?v, ?nx) &*& StackList(nx, count - 1));
@*/

class Stack {
    private Node head;

    //@ predicate valid(int count) = this.head |-> ?h &*& StackList(h, count) &*& count >= 0;

    /*@
      requires true;
      ensures valid(0);
    @*/
    public Stack()
    {
        head = null;
    }

    /*@
      requires valid(?count);
      ensures valid(count) &*& (count == 0 ? result == true : result == false);
    @*/
    public boolean isEmpty()
    {
        return head == null;
    }

    /*@
      requires valid(?count) &*& count > 0;
      ensures valid(count - 1) &*& result == _;
    @*/
    public int pop()
    {
        int val = head.val;
        Node next = head.getNext();
        head = next;
        return val;
    }
}