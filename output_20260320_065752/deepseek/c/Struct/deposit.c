#include "stdlib.h"

struct account
{
    int balance;
};

/*@
predicate account(struct account *a;) = a->balance |-> _;
@*/

struct account *create_account()
//@ requires true;
//@ ensures account(result) &*& malloc_block_account(result);
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    //@ close account(myAccount);
    myAccount->balance = 0;
    return myAccount;
}

void account_deposit(struct account *myAccount, int amount)
//@ requires account(myAccount);
//@ ensures account(myAccount);
{
    //@ open account(myAccount);
    myAccount->balance += amount;
    //@ close account(myAccount);
}

int account_get_balance(struct account *myAccount)
//@ requires account(myAccount);
//@ ensures account(myAccount);
{
    //@ open account(myAccount);
    int result = myAccount->balance;
    //@ close account(myAccount);
    return result;
}

void account_set_balance(struct account *myAccount, int newBalance)
//@ requires account(myAccount);
//@ ensures account(myAccount);
{
    //@ open account(myAccount);
    myAccount->balance = newBalance;
    //@ close account(myAccount);
}

void account_dispose(struct account *myAccount)
//@ requires account(myAccount) &*& malloc_block_account(myAccount);
//@ ensures true;
{
    //@ open account(myAccount);
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
    account_dispose(myAccount);
    return 0;
}