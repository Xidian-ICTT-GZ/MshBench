class Node {

    int value;
    Node next;

}













class Stack {

    Node head;
    
    
    
    Stack()
        
        
    {
        
    }
    
    void push(int element)
        
        
    {
        
        Node n = new Node();
        n.value = element;
        n.next = head;
        head = n;
        
        
    }
    
    int pop()
        
        
    {
        
        
        int result = head.value;
        head = head.next;
        
        return result;
    }

}

class Program {

    public static void main(String[] args)
        
        
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