#include "stdlib.h"

//@ predicate Account(struct account *acc, int limit, int balance) = acc->limit |-> limit &*& acc->balance |-> balance;

struct account
{
    int limit;
    int balance;
};

//@ requires true; @ensures result == create_account(limit);
struct account *create_account(int limit)
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

//@ requires valid(myAccount) &*& Account(myAccount, _, _); @ensures result == myAccount->balance;
int account_get_balance(struct account *myAccount)
{
    int result = myAccount->balance;
    
    return result;
}

//@ requires valid(myAccount) &*& Account(myAccount, _, ?bal); @ensures Account(myAccount, _, bal + amount);
void account_deposit(struct account *myAccount, int amount)
{
    myAccount->balance += amount;
    
}

//@ requires valid(myAccount) &*& Account(myAccount, limit, bal); @ensures result == (bal - amount < limit ? bal - limit : amount) &*& Account(myAccount, limit, bal - ((bal - amount < limit ? bal - limit : amount)));
int account_withdraw(struct account *myAccount, int amount)
{
    int result = myAccount->balance - amount < myAccount->limit ? myAccount->balance - myAccount->limit : amount;
    myAccount->balance -= result;
    
    return result;
}

//@ requires valid(myAccount) &*& Account(myAccount, _, _); @ensures true;
void account_dispose(struct account *myAccount)
{
    free(myAccount);
}

//@ requires true; @ensures true;
int main()
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