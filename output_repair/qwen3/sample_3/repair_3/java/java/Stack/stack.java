class Node {
    Node nxt;
    int val;

    /*@
      predicate Node(Node n, int v; Node next) =
        n.nxt |-> next &*& n.val |-> v;
    @*/

    /*@
      requires true;
      ensures Node(this, v, n);
    @*/
    Node(Node n, int v) {
        nxt = n;
        val = v;
    }

    /*@
      requires Node(this, ?v, ?nx);
      ensures Node(this, v, nx) &*& result == nx;
    @*/
    Node getNext() {
        return nxt;
    }

    /*@
      requires Node(this, ?v, ?nx);
      ensures Node(this, v, nx) &*& result == v;
    @*/
    int getValue() {
        return val;
    }
}

/*@ predicate NodeList(Node n, int count) =
      (n == null &*& count == 0) ||
      (n != null &*& count > 0 &*& Node(n, _, ?next) &*& NodeList(next, count - 1));
@*/

class Stack {
    private Node head;

    /*@
      requires true;
      ensures this.head |-> null &*& NodeList(null, 0);
    @*/
    public Stack() {
        head = null;
    }

    /*@
      requires this.head |-> ?h &*& NodeList(h, ?c);
      ensures this.head |-> h &*& NodeList(h, c) &*& (h == null ? result == true : result == false);
    @*/
    public boolean isEmpty() {
        return head == null;
    }

    /*@
      requires this.head |-> ?h &*& h != null &*& NodeList(h, ?c) &*& c > 0;
      ensures this.head |-> ?nx &*& NodeList(nx, c - 1) &*& result == ?v;
    @*/
    public int pop() {
        int val = head.val;
        Node next = head.getNext();
        head = next;
        return val;
    }
}