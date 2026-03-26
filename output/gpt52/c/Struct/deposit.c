#include "stdlib.h"

/*@

predicate account(struct account *a; int bal) =
    a->balance |-> bal;

@*/

struct account
{
    int balance;
};

struct account *create_account()

//@ requires true;
//@ ensures account(result, 0);
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    //@ assume(myAccount != 0);
    myAccount->balance = 0;
    //@ close account(myAccount, 0);
    return myAccount;
}

void account_deposit(struct account *myAccount, int amount)

//@ requires account(myAccount, ?bal);
//@ ensures account(myAccount, bal + amount);
{
    //@ open account(myAccount, bal);
    myAccount->balance += amount;
    //@ close account(myAccount, bal + amount);
}

int account_get_balance(struct account *myAccount)

//@ requires account(myAccount, ?bal);
//@ ensures account(myAccount, bal) &*& result == bal;
{
    //@ open account(myAccount, bal);
    int result = myAccount->balance;
    //@ close account(myAccount, bal);
    return result;
}

void account_set_balance(struct account *myAccount, int newBalance)

//@ requires account(myAccount, ?bal);
//@ ensures account(myAccount, newBalance);
{
    //@ open account(myAccount, bal);
    myAccount->balance = newBalance;
    //@ close account(myAccount, newBalance);
}

void account_dispose(struct account *myAccount)

//@ requires account(myAccount, ?bal);
//@ ensures true;
{
    //@ open account(myAccount, bal);
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