#include "stdlib.h"

/*@ predicate account(struct account *a; int limit, int balance) =
      a->limit |-> limit &*& a->balance |-> balance;
 @*/

struct account
{
    int limit;
    int balance;
};

struct account *create_account(int limit)
    //@ requires true;
    //@ ensures account(result, limit, 0);
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->limit = limit;
    myAccount->balance = 0;
    
    return myAccount;
}

int account_get_balance(struct account *myAccount)
    //@ requires account(myAccount, ?limit, ?balance);
    //@ ensures account(myAccount, limit, balance) &*& result == balance;
{
    
    int result = myAccount->balance;
    
    return result;
}

void account_deposit(struct account *myAccount, int amount)
    //@ requires account(myAccount, ?limit, ?balance);
    //@ ensures account(myAccount, limit, balance + amount);
{
    
    myAccount->balance += amount;
    
}

int account_withdraw(struct account *myAccount, int amount)
    //@ requires account(myAccount, ?limit, ?balance);
    /*@ ensures
          account(myAccount, limit, balance - result) &*&
          result == (balance - amount < limit ? balance - limit : amount);
    @*/
{
    
    int result = myAccount->balance - amount < myAccount->limit ? myAccount->balance - myAccount->limit : amount;
    myAccount->balance -= result;
    
    return result;
}

void account_dispose(struct account *myAccount)
    //@ requires account(myAccount, _, _);
    //@ ensures true;
{
    
    free(myAccount);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct account *myAccount = create_account(-100);
    account_deposit(myAccount, 200);
    int w1 = account_withdraw(myAccount, 50);
    assert(w1 == 50);
    int b1 = account_get_balance(myAccount);
    assert(b1 == 150);
    int w2 = account_withdraw(myAccount, 300);
    assert(w2 == 250);
    int b2 = account_get_balance(myAccount);
    assert(b2 == -100);
    account_dispose(myAccount);
    return 0;
}