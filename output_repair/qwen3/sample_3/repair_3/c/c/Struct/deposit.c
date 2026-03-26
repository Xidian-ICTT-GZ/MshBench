#include "stdlib.h"
#include "assert.h"

struct account
{
    int balance;
};

/*@ predicate account(struct account *a; int b) = a->balance |-> b; @*/

//@ requires true
//@ ensures account(result, 0)
struct account *create_account()
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->balance = 0;
    return myAccount;
}

//@ requires account(myAccount, ?old_balance)
//@ ensures account(myAccount, old_balance + amount)
void account_deposit(struct account *myAccount, int amount)
{
    myAccount->balance += amount;
}

//@ requires account(myAccount, ?b)
//@ ensures account(myAccount, b) &*& result == b
int account_get_balance(struct account *myAccount)
{
    int result = myAccount->balance;
    return result;
}

//@ requires account(myAccount, ?old_balance)
//@ ensures account(myAccount, newBalance)
void account_set_balance(struct account *myAccount, int newBalance)
{
    myAccount->balance = newBalance;
}

//@ requires account(myAccount, ?b)
//@ ensures true
void account_dispose(struct account *myAccount)
{
    free(myAccount);
}

//@ requires true
//@ ensures true
int main()
{
    struct account *myAccount = create_account();
    account_set_balance(myAccount, 5);
    account_deposit(myAccount, 10);
    int b = account_get_balance(myAccount);
    assert(b == 15);
    account_dispose(myAccount);
    return 0;
}