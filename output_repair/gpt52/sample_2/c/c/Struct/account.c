#include "stdlib.h"

struct account
{
    int balance;
};

/*@ predicate account(struct account *a) = a->balance |-> _; @*/

//@ requires true;
//@ ensures account(result) &*& result != 0;
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

//@ requires account(myAccount);
//@ ensures account(myAccount);
void account_set_balance(struct account *myAccount, int newBalance)
{
    myAccount->balance = newBalance;
}

//@ requires account(myAccount);
//@ ensures true;
void account_dispose(struct account *myAccount)
{
    free(myAccount);
}

//@ requires true;
//@ ensures true;
int main()
{
    struct account *myAccount = create_account();
    account_set_balance(myAccount, 5);
    account_dispose(myAccount);
    return 0;
}