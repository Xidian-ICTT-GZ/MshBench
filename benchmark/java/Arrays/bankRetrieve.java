



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

    












    public Account retrieveLastAccount()
    
    
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}
