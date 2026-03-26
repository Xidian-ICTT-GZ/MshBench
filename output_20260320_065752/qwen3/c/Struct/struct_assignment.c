/*@ predicate foo(struct foo f;) @*/
/*@ predicate bar(struct bar b;) @*/

void test()
//@ requires true;
//@ ensures true;
{
    struct foo a = {1, 2};
    //@ close foo(a);
    struct foo b = {3, 4};
    //@ close foo(b);
    
    struct bar r = {{5, 6}, {7, 8}};
    //@ close foo(r.p);
    //@ close foo(r.q);
    //@ close bar(r);
    struct bar t;
    //@ close foo(t.p);
    //@ close foo(t.q);
    //@ close bar(t);
    
    t.p.x = 10;
    t.p.y = 20;
    //@ open foo(t.p);
    //@ close foo(t.p);
    t.q.x = 30;
    t.q.y = 40;
    //@ open foo(t.q);
    //@ close foo(t.q);

    //@ open foo(a);
    //@ open foo(b);
    a = b;
    //@ close foo(a);
    //@ close foo(b);
    
    //@ open bar(r);
    //@ open foo(r.p);
    //@ open foo(r.q);
    r.p = r.q;
    //@ close foo(r.p);
    //@ close foo(r.q);
    //@ close bar(r);
    
    //@ open bar(r);
    //@ open foo(r.q);
    //@ open bar(t);
    //@ open foo(t.p);
    r.q = t.p;
    //@ close foo(r.q);
    //@ close bar(r);
    //@ close foo(t.p);
    //@ close bar(t);
    
    //@ open foo(a);
    //@ open bar(r);
    //@ open foo(r.p);
    a = r.p;
    //@ close foo(a);
    //@ close foo(r.p);
    //@ close bar(r);
    
    //@ open foo(t.p);
    //@ open foo(b);
    t.p = b;
    //@ close foo(t.p);
    //@ close foo(b);
    
    //@ open bar(r);
    //@ open bar(t);
    r = t;
    //@ close bar(r);
    //@ close bar(t);
}

void test2()
//@ requires true;
//@ ensures true;
{
    struct foo a = {1, 2};
    //@ close foo(a);
    struct foo b = {3, 4};
    //@ close foo(b);
    
    struct bar r;
    //@ close foo(r.p);
    //@ close foo(r.q);
    //@ close bar(r);
    struct bar t;
    //@ close foo(t.p);
    //@ close foo(t.q);
    //@ close bar(t);
    
    //@ open bar(r);
    //@ open foo(r.q);
    //@ open foo(a);
    r.q = a;
    //@ close foo(r.q);
    //@ close bar(r);
    //@ close foo(a);
    
    //@ open bar(t);
    //@ open foo(t.p);
    //@ open foo(b);
    t.p = b;
    //@ close foo(t.p);
    //@ close bar(t);
    //@ close foo(b);
    
    //@ open foo(a);
    //@ open foo(b);
    a = b;
    //@ close foo(a);
    //@ close foo(b);
    
    //@ open bar(r);
    //@ open foo(r.p);
    //@ open foo(r.q);
    r.p = r.q;
    //@ close foo(r.p);
    //@ close foo(r.q);
    //@ close bar(r);
    
    //@ open bar(r);
    //@ open foo(r.q);
    //@ open bar(t);
    //@ open foo(t.p);
    r.q = t.p;
    //@ close foo(r.q);
    //@ close bar(r);
    //@ close foo(t.p);
    //@ close bar(t);
    
    //@ open foo(a);
    //@ open bar(r);
    //@ open foo(r.p);
    a = r.p;
    //@ close foo(a);
    //@ close foo(r.p);
    //@ close bar(r);
    
    //@ open bar(t);
    //@ open foo(t.q);
    //@ open foo(b);
    t.q = b;
    //@ close foo(t.q);
    //@ close bar(t);
    //@ close foo(b);
    
    //@ open bar(r);
    //@ open bar(t);
    r = t;
    //@ close bar(r);
    //@ close bar(t);
}

void test3()
//@ requires true;
//@ ensures true;
{
    struct foo a = {1, 2};
    //@ close foo(a);
    struct foo b = {3, 4};
    //@ close foo(b);
    
    struct bar r;
    //@ close foo(r.p);
    //@ close foo(r.q);
    //@ close bar(r);
    struct bar t;
    //@ close foo(t.p);
    //@ close foo(t.q);
    //@ close bar(t);
    
    //@ open bar(r);
    //@ open foo(r.q);
    //@ open foo(a);
    r.q = a;
    //@ close foo(r.q);
    //@ close bar(r);
    //@ close foo(a);
    
    //@ open bar(t);
    //@ open foo(t.p);
    //@ open foo(b);
    t.p = b;
    //@ close foo(t.p);
    //@ close bar(t);
    //@ close foo(b);
    
    //@ open bar(t);
    //@ open foo(t.q);
    //@ open foo(a);
    t.q = a;
    //@ close foo(t.q);
    //@ close bar(t);
    //@ close foo(a);
    
    //@ open foo(a);
    //@ open foo(b);
    a = b;
    //@ close foo(a);
    //@ close foo(b);
    
    //@ open bar(r);
    //@ open foo(r.p);
    //@ open foo(r.q);
    r.p = r.q;
    //@ close foo(r.p);
    //@ close foo(r.q);
    //@ close bar(r);
    
    //@ open bar(r);
    //@ open foo(r.q);
    //@ open bar(t);
    //@ open foo(t.p);
    r.q = t.p;
    //@ close foo(r.q);
    //@ close bar(r);
    //@ close foo(t.p);
    //@ close bar(t);
    
    //@ open foo(a);
    //@ open bar(r);
    //@ open foo(r.p);
    a = r.p;
    //@ close foo(a);
    //@ close foo(r.p);
    //@ close bar(r);
    
    //@ open foo(t.p);
    //@ open foo(b);
    t.p = b;
    //@ close foo(t.p);
    //@ close foo(b);
    
    //@ open bar(r);
    //@ open bar(t);
    r = t;
    //@ close bar(r);
    //@ close bar(t);
}

void test4(struct foo f)
//@ requires foo(f);
//@ ensures true;
{
    //@ open foo(f);
}

struct foo test5()
//@ requires true;
//@ ensures foo(result);
{
    test4((struct foo) { 20, 30 });
    //@ close foo((struct foo){40, 50});
    return (struct foo) { 40, 50 };
}

struct foo test6()
//@ requires true;
//@ ensures foo(result);
{
    test4((struct foo) { .y = 30, .x = 20 });
    //@ close foo((struct foo){.y = 50, .x = 40});
    return (struct foo) { .y = 50, .x = 40 };
}