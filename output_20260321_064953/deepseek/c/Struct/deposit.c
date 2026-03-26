#include "stdlib.h"

struct account
{
    int balance;
};

/*@
predicate account(struct account *a; int balance) =
    a->balance |-> balance
    &*& malloc_block_account(a);
@*/

struct account *create_account()
//@ requires true;
//@ ensures account(result, 0);
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    //@ close account(myAccount, 0);
    myAccount->balance = 0;
    return myAccount;
}

void account_deposit(struct account *myAccount, int amount)
//@ requires account(myAccount, ?old);
//@ ensures account(myAccount, old + amount);
{
    //@ open account(myAccount, old);
    myAccount->balance += amount;
    //@ close account(myAccount, old + amount);
}

int account_get_balance(struct account *myAccount)
//@ requires account(myAccount, ?b);
//@ ensures account(myAccount, b) &*& result == b;
{
    //@ open account(myAccount, b);
    int result = myAccount->balance;
    //@ close account(myAccount, b);
    return result;
}

void account_set_balance(struct account *myAccount, int newBalance)
//@ requires account(myAccount, ?old);
//@ ensures account(myAccount, newBalance);
{
    //@ open account(myAccount, old);
    myAccount->balance = newBalance;
    //@ close account(myAccount, newBalance);
}

void account_dispose(struct account *myAccount)
//@ requires account(myAccount, _);
//@ ensures true;
{
    //@ open account(myAccount, _);
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
    //@ assert b == 15;
    assert(b == 15);
    account_dispose(myAccount);
    return 0;
}