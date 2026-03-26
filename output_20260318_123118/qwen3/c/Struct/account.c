/*@ predicate account(struct account *a; int balance) = a->balance |-> balance; @*/

struct account
{
    int balance;
};

//@ requires true;
//@ ensures account(result, 0);
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

//@ requires account(myAccount, ?old_balance);
//@ ensures account(myAccount, newBalance);
void account_set_balance(struct account *myAccount, int newBalance)
{
    myAccount->balance = newBalance;
}

//@ requires account(myAccount, ?balance);
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