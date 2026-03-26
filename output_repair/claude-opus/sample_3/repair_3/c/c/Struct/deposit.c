#include "stdlib.h"

struct account
{
    int balance;
};

/*@ predicate account(struct account *a; int b) = malloc_block_account(a) &*& a->balance |-> b; @*/

struct account *create_account()
//@ requires true;
//@ ensures account(result, 0);
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->balance = 0;
    return myAccount;
}

void account_deposit(struct account *myAccount, int amount)
//@ requires account(myAccount, ?b) &*& INT_MIN - b <= amount &*& amount <= INT_MAX - b;
//@ ensures account(myAccount, b + amount);
{
    myAccount->balance += amount;
}

int account_get_balance(struct account *myAccount)
//@ requires account(myAccount, ?b);
//@ ensures account(myAccount, b) &*& result == b;
{
    int result = myAccount->balance;
    return result;
}

void account_set_balance(struct account *myAccount, int newBalance)
//@ requires account(myAccount, _);
//@ ensures account(myAccount, newBalance);
{
    myAccount->balance = newBalance;
}

void account_dispose(struct account *myAccount)
//@ requires account(myAccount, _);
//@ ensures true;
{
    free(myAccount);
}

int main()
//@ requires true;
//@ ensures true;
{
    struct account *myAccount = create_account();
    account_set_balance(myAccount, 5);
    account_deposit(myAccount, 10);
    int b = account_get_balance(myAccount);
    assert(b == 15);
    account_dispose(myAccount);
    return 0;
}