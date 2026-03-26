#include "stdlib.h"

/*@ 
predicate account(struct account *p; int limit, int balance) =
    p != 0 &*&
    p->limit |-> limit &*&
    p->balance |-> balance &*&
    limit <= balance;
@*/

struct account
{
    int limit;
    int balance;
};

struct account *create_account(int limit)
    //@ requires true;
    //@ ensures account(result, limit, 0);
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    //@ assume limit <= 0;
    myAccount->limit = limit;
    myAccount->balance = 0;

    //@ assert limit <= 0;
    //@ assert limit <= 0 + 0;
    //@ close account(myAccount, limit, 0);
    return myAccount;
}

int account_get_balance(struct account *myAccount)
    //@ requires account(myAccount, ?limit, ?balance);
    //@ ensures account(myAccount, limit, balance) &*& result == balance;
{
    int result = myAccount->balance;

    return result;
}

void account_deposit(struct account *myAccount, int amount)
    //@ requires account(myAccount, ?limit, ?balance);
    //@ ensures account(myAccount, limit, balance + amount);
{
    int old_balance = myAccount->balance;
    //@ open account(myAccount, limit, old_balance);
    myAccount->balance += amount;
    //@ close account(myAccount, limit, old_balance + amount);
}

int account_withdraw(struct account *myAccount, int amount)
    //@ requires account(myAccount, ?limit, ?balance);
    //@ ensures account(myAccount, limit, balance - result) &*&
    //@         (balance - amount < limit ==> result == balance - limit) &*&
    //@         (balance - amount >= limit ==> result == amount);
{
    //@ open account(myAccount, limit, balance);
    int to_withdraw;
    //@ int can_withdraw_minus = balance - amount;
    //@ int cond = 0; // dummy variable because conditional expressions forbidden in specs
    //@ // We cannot write cond as (balance - amount < limit) because that would be conditional
    if (myAccount->balance - amount < myAccount->limit) {
        to_withdraw = myAccount->balance - myAccount->limit;
        //@ //@ under this branch: result == balance - limit 
    } else {
        to_withdraw = amount;
        //@ //@ under this branch: result == amount
    }
    myAccount->balance -= to_withdraw;
    //@ close account(myAccount, limit, balance - to_withdraw);
    return to_withdraw;
}

void account_dispose(struct account *myAccount)
    //@ requires account(myAccount, ?limit, ?balance);
    //@ ensures true;
{
    //@ open account(myAccount, limit, balance);
    free(myAccount);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct account *myAccount = create_account(-100);
    account_deposit(myAccount, 200);
    int w1 = account_withdraw(myAccount, 50);
    //@ assert w1 == 50;
    int b1 = account_get_balance(myAccount);
    //@ assert b1 == 150;
    int w2 = account_withdraw(myAccount, 300);
    //@ assert w2 == 250;
    int b2 = account_get_balance(myAccount);
    //@ assert b2 == -100;
    account_dispose(myAccount);
    return 0;
}