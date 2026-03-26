#include "stdlib.h"

/*@ predicate account(struct account *a; int balance) =
      a->balance |-> balance;
@*/

struct account
{
    int balance;
};

/*@ 
  requires true;
  ensures account(result, 0);
@*/
struct account *create_account()
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->balance = 0;
    //@ close account(myAccount, 0);
    return myAccount;
}

/*@
  requires account(myAccount, ?balance) &*& 0 <= amount;
  ensures account(myAccount, balance + amount);
@*/
void account_deposit(struct account *myAccount, int amount)
{
    //@ open account(myAccount, ?balance);
    myAccount->balance += amount;
    //@ close account(myAccount, balance + amount);
}

/*@
  requires account(myAccount, ?balance);
  ensures account(myAccount, balance) &*& result == balance;
@*/
int account_get_balance(struct account *myAccount)
{
    //@ open account(myAccount, ?balance);
    int result = myAccount->balance;
    //@ close account(myAccount, balance);
    return result;
}

/*@
  requires account(myAccount, ?balance);
  ensures account(myAccount, newBalance);
@*/
void account_set_balance(struct account *myAccount, int newBalance)
{
    //@ open account(myAccount, _);
    myAccount->balance = newBalance;
    //@ close account(myAccount, newBalance);
}

/*@
  requires account(myAccount, _);
  ensures true;
@*/
void account_dispose(struct account *myAccount)
{
    //@ open account(myAccount, _);
    free(myAccount);
}

int main()
/*@
  requires true;
  ensures true;
@*/
{
    struct account *myAccount = create_account();
    account_set_balance(myAccount, 5);
    account_deposit(myAccount, 10);
    int b = account_get_balance(myAccount);
    assert(b == 15);
    account_dispose(myAccount);
    return 0;
}