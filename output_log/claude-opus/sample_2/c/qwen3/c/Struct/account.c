#include "stdlib.h"

/*@ predicate account(struct account *p; int balance) =
    p != 0 &*&
    malloc_block_account(p) &*&
    p->balance |-> balance;
@*/

struct account
{
    int balance;
};

struct account *create_account()

{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    //@ assume myAccount != 0;
    //@ leak malloc_block_account(myAccount);
    myAccount->balance = 0;
    //@ assert myAccount->balance |-> 0;
    //@ produce account(myAccount, 0);
    return myAccount;
}

void account_set_balance(struct account *myAccount, int newBalance)

{
    //@ requires account(myAccount, ?oldBalance);
    //@ ensures account(myAccount, newBalance);
    myAccount->balance = newBalance;
    //@ assert myAccount->balance |-> newBalance;
    //@ produce account(myAccount, newBalance);
}

void account_dispose(struct account *myAccount)

{
    //@ requires account(myAccount, ?balance);
    //@ ensures true;
    free(myAccount);
    //@ leak malloc_block_account(myAccount);
}

int main()

{
    struct account *myAccount = create_account();
    //@ assert account(myAccount, 0);
    account_set_balance(myAccount, 5);
    //@ assert account(myAccount, 5);
    account_dispose(myAccount);
    return 0;
}