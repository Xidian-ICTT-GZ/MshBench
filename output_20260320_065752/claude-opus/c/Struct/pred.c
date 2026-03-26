#include "stdlib.h"

/*@ 
predicate account(struct account *a; int limit, int balance) = 
  malloc_block_account(a) &*&
  a->limit |-> limit &*& a->balance |-> balance;
@*/

struct account
{
    int limit;
    int balance;
};

/*@
requires true;
ensures result != 0 &*& account(result, limit, 0);
@*/
struct account *create_account(int limit)

{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->limit = limit;
    myAccount->balance = 0;
    
    return myAccount;
}

/*@
requires account(myAccount, ?limit, ?balance);
ensures account(myAccount, limit, balance) &*& result == balance;
@*/
int account_get_balance(struct account *myAccount)

{
    
    int result = myAccount->balance;
    
    return result;
}

/*@
requires account(myAccount, ?limit, ?balance) &*& amount >= 0;
ensures account(myAccount, limit, balance + amount);
@*/
void account_deposit(struct account *myAccount, int amount)

{
    
    myAccount->balance += amount;
    
}

/*@
requires account(myAccount, ?limit, ?balance) &*& amount >= 0;
ensures account(myAccount, limit, balance - result) &*& 
        (result == (balance - amount < limit ? balance - limit : amount)) &*&
        result >= 0;
@*/
int account_withdraw(struct account *myAccount, int amount)

{
    
    int result = myAccount->balance - amount < myAccount->limit ? myAccount->balance - myAccount->limit : amount;
    myAccount->balance -= result;
    
    return result;
}

/*@
requires account(myAccount, ?, ?);
ensures true;
@*/
void account_dispose(struct account *myAccount)

{
    
    free(myAccount);
}

int main()

{
    struct account *myAccount = create_account(-100);
    account_deposit(myAccount, 200);
    int w1 = account_withdraw(myAccount, 50);
    assert(w1 == 50);
    int b1 = account_get_balance(myAccount);
    assert(b1 == 150);
    int w2 = account_withdraw(myAccount, 300);
    assert(w2 == 250);
    int b2 = account_get_balance(myAccount);
    assert(b2 == -100);
    account_dispose(myAccount);
    return 0;
}