class Node {
    Node nxt;
    int val;

    /*@
      predicate Node(Node nxt, int val) = this.nxt |-> nxt &*& this.val |-> val;
    @*/

    /*@
      requires true;
      ensures Node(n, v);
    @*/
    Node(Node n, int v) {
        nxt = n;
        val = v;
    }

    /*@
      requires Node(?nx, ?v);
      ensures Node(nx, v) &*& result == nx;
    @*/
    Node getNext() {
        return nxt;
    }

    /*@
      requires Node(?nx, ?v);
      ensures Node(nx, v) &*& result == v;
    @*/
    int getValue() {
        return val;
    }
}

/*@ predicate NodeList(Node n, int count) =
      (n == null &*& count == 0) ||
      (n != null &*& count > 0 &*& Node(?nx, _) &*& NodeList(nx, count - 1));
@*/

class Stack {
    private Node head;

    /*@
      predicate Stack(Node head) = this.head |-> head;
    @*/

    /*@
      requires true;
      ensures Stack(null);
    @*/
    public Stack() {
        head = null;
    }

    /*@
      requires Stack(?h);
      ensures Stack(h) &*& result == (h == null);
    @*/
    public boolean isEmpty() {
        return head == null;
    }

    /*@
      requires Stack(?h) &*& h != null &*& Node(?nx, ?v) &*& NodeList(nx, ?c) &*& c >= 0;
      ensures Stack(nx) &*& NodeList(nx, c) &*& result == v;
    @*/
    public int pop() {
        int val = head.val;
        Node next = head.getNext();
        head = next;
        return val;
    }
}