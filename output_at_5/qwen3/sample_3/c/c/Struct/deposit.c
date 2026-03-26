#include "stdlib.h"

/*@
predicate account(struct account *acc, int balance) = acc->balance |-> balance &*& acc != 0;
@*/

struct account
{
    int balance;
};

//@ requires true;
//@ ensures \result != 0 ==> account(\result, 0);
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

//@ requires account(myAccount, ?bal);
//@ requires amount >= 0;
//@ ensures account(myAccount, bal + amount);
void account_deposit(struct account *myAccount, int amount)
{
    myAccount->balance += amount;
}

//@ requires account(myAccount, ?bal);
//@ ensures \result == bal;
int account_get_balance(struct account *myAccount)
{
    int result = myAccount->balance;
    return result;
}

//@ requires account(myAccount, ?bal);
//@ requires newBalance >= 0;
//@ ensures account(myAccount, newBalance);
void account_set_balance(struct account *myAccount, int newBalance)
{
    myAccount->balance = newBalance;
}

//@ requires account(myAccount, ?bal);
//@ ensures true;
void account_dispose(struct account *myAccount)
{
    free(myAccount);
}

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