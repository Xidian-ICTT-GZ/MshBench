class Account {
    int balance;

    public Account()
    
    
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    

    public Bank(int cap)
    
    
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    public void addNewAccount()
    
    
    {
        Account c = new Account();
        store[nelems] = c;
        
        nelems = nelems + 1;
    }
}