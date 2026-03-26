struct foo {
    int x;
    int y;
};

struct bar {
    struct foo p;
    struct foo q;
};

/*@
predicate foo(struct foo f;) = true;
predicate bar(struct bar b;) = true;
@*/

//@ requires true;
//@ ensures true;
void test()
{
    struct foo a = {1, 2};
    //@ close foo(a);
    struct foo b = {3, 4};
    //@ close foo(b);
    
    struct bar r = {{5, 6}, {7, 8}};
    //@ close bar(r);
    struct bar t;
    //@ close bar(t);
    
    //@ open bar(t);
    t.p.x = 10;
    t.p.y = 20;
    t.q.x = 30;
    t.q.y = 40;
    //@ close bar(t);

    //@ open foo(a);
    //@ open foo(b);
    a = b;
    //@ close foo(a);
    
    //@ open bar(r);
    r.p = r.q;
    //@ close bar(r);
    
    //@ open bar(r);
    //@ open bar(t);
    r.q = t.p;
    //@ close bar(r);
    //@ close bar(t);
    
    //@ open foo(a);
    //@ open bar(r);
    a = r.p;
    //@ close foo(a);
    //@ close bar(r);
    
    //@ open bar(t);
    //@ open foo(b);
    t.p = b;
    //@ close bar(t);
    //@ close foo(b);
    
    //@ open bar(r);
    //@ open bar(t);
    r = t;
    //@ close bar(r);
    //@ close bar(t);
}

//@ requires true;
//@ ensures true;
void test2()
{
    struct foo a = {1, 2};
    //@ close foo(a);
    struct foo b = {3, 4};
    //@ close foo(b);
    
    struct bar r;
    //@ close bar(r);
    struct bar t;
    //@ close bar(t);

    //@ open bar(r);
    //@ open foo(a);
    r.q = a;
    //@ close bar(r);
    //@ close foo(a);
    
    //@ open bar(t);
    //@ open foo(b);
    t.p = b;
    //@ close bar(t);
    //@ close foo(b);
    
    //@ open foo(a);
    //@ open foo(b);
    a = b;
    //@ close foo(a);
    
    //@ open bar(r);
    r.p = r.q;
    //@ close bar(r);
    
    //@ open bar(r);
    //@ open bar(t);
    r.q = t.p;
    //@ close bar(r);
    //@ close bar(t);
    
    //@ open foo(a);
    //@ open bar(r);
    a = r.p;
    //@ close foo(a);
    //@ close bar(r);
    
    //@ open bar(t);
    //@ open foo(b);
    t.q = b;
    //@ close bar(t);
    //@ close foo(b);
    
    //@ open bar(r);
    //@ open bar(t);
    r = t;
    //@ close bar(r);
    //@ close bar(t);
}

//@ requires true;
//@ ensures true;
void test3()
{
    struct foo a = {1, 2};
    //@ close foo(a);
    struct foo b = {3, 4};
    //@ close foo(b);
    
    struct bar r;
    //@ close bar(r);
    struct bar t;
    //@ close bar(t);

    //@ open bar(r);
    //@ open foo(a);
    r.q = a;
    //@ close bar(r);
    //@ close foo(a);
    
    //@ open bar(t);
    //@ open foo(b);
    t.p = b;
    //@ close bar(t);
    //@ close foo(b);
    
    //@ open bar(t);
    //@ open foo(a);
    t.q = a;
    //@ close bar(t);
    //@ close foo(a);
    
    //@ open foo(a);
    //@ open foo(b);
    a = b;
    //@ close foo(a);
    
    //@ open bar(r);
    r.p = r.q;
    //@ close bar(r);
    
    //@ open bar(r);
    //@ open bar(t);
    r.q = t.p;
    //@ close bar(r);
    //@ close bar(t);
    
    //@ open foo(a);
    //@ open bar(r);
    a = r.p;
    //@ close foo(a);
    //@ close bar(r);
    
    //@ open bar(t);
    //@ open foo(b);
    t.p = b;
    //@ close bar(t);
    //@ close foo(b);
    
    //@ open bar(r);
    //@ open bar(t);
    r = t;
    //@ close bar(r);
    //@ close bar(t);
}

//@ requires true;
//@ ensures true;
void test4(struct foo f)
//@ requires foo(f);
//@ ensures foo(f);
{
    //@ open foo(f);
    //@ close foo(f);
}

//@ requires true;
//@ ensures foo(result);
struct foo test5()
{
    struct foo tmp1 = { 20, 30 };
    //@ close foo(tmp1);
    test4(tmp1);
    //@ open foo(tmp1);
    struct foo tmp2 = { 40, 50 };
    //@ close foo(tmp2);
    return tmp2;
}

//@ requires true;
//@ ensures foo(result);
struct foo test6()
{
    struct foo tmp1 = { .y = 30, .x = 20 };
    //@ close foo(tmp1);
    test4(tmp1);
    //@ open foo(tmp1);
    struct foo tmp2 = { .y = 50, .x = 40 };
    //@ close foo(tmp2);
    return tmp2;
}