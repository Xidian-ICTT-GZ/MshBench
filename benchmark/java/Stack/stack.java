class Node {
    Node nxt;
    int val;

    Node(Node n, int v)
        
        
    {
        nxt = n;
        val = v;
    }

    Node getNext()
        
        
    {
        return nxt;
    }

    int getValue()
        
        
    {
        return val;
    }
}

















class Stack {
    private Node head;

    public Stack()
        
        
    {
        head = null;
        
    }

    public boolean isEmpty()
        
        
    {
        return head == null;
    }

    public int pop()
        
        
    {
        
        
        

        int val = head.val;
        Node next = head.getNext();
        head = next;
        
        return val;
    }
}
