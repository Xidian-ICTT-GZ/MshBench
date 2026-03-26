#include "stdlib.h"

/*@
predicate account(struct account *a; int balance) = a->balance |-> balance;
@*/

struct account *create_account()

{
    //@ requires true;
    //@ ensures account(result, 0);
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->balance = 0;
    //@ close account(myAccount, 0);
    return myAccount;
}

void account_deposit(struct account *myAccount, int amount)

{
    //@ requires account(myAccount, ?b);
    //@ ensures account(myAccount, b + amount);
    //@ open account(myAccount, _);
    myAccount->balance += amount;
    //@ close account(myAccount, myAccount->balance);
}

int account_get_balance(struct account *myAccount)

{
    //@ requires account(myAccount, ?b);
    //@ ensures account(myAccount, b) &*& result == b;
    //@ open account(myAccount, _);
    int result = myAccount->balance;
    //@ close account(myAccount, result);
    return result;
}

void account_set_balance(struct account *myAccount, int newBalance)

{
    //@ requires account(myAccount, ?b);
    //@ ensures account(myAccount, newBalance);
    //@ open account(myAccount, _);
    myAccount->balance = newBalance;
    //@ close account(myAccount, newBalance);
}

void account_dispose(struct account *myAccount)

{
    //@ requires account(myAccount, _);
    //@ ensures true;
    //@ open account(myAccount, _);
    free(myAccount);
}

int main()

{
    //@ requires true;
    //@ ensures true;
    struct account *myAccount = create_account();
    account_set_balance(myAccount, 5);
    account_deposit(myAccount, 10);
    int b = account_get_balance(myAccount);
    assert(b == 15);
    account_dispose(myAccount);
    return 0;
}