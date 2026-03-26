struct foo
{
    int x;
    int y;
};

struct bar
{
    struct foo p;
    struct foo q;
};

//@ requires true;
//@ ensures true;
void test()
{
    struct foo a = {1, 2};
    struct foo b = {3, 4};

    struct bar r = {{5, 6}, {7, 8}};
    struct bar t;

    t.p.x = 10;
    t.p.y = 20;
    t.q.x = 30;
    t.q.y = 40;

    a = b;

    r.p = r.q;

    r.q = t.p;

    a = r.p;

    t.p = b;

    r = t;
}

//@ requires true;
//@ ensures true;
void test2()
{
    struct foo a = {1, 2};
    struct foo b = {3, 4};

    struct bar r;
    struct bar t;

    r.q = a;

    t.p = b;

    a = b;

    r.p = r.q;

    r.q = t.p;

    a = r.p;

    t.q = b;

    r = t;
}

//@ requires true;
//@ ensures true;
void test3()
{
    struct foo a = {1, 2};
    struct foo b = {3, 4};

    struct bar r;
    struct bar t;

    r.q = a;
    t.p = b;
    t.q = a;
    a = b;
    r.p = r.q;
    r.q = t.p;
    a = r.p;
    t.p = b;

    r = t;
}

//@ requires true;
//@ ensures true;
void test4(struct foo f)
{
}

//@ requires true;
//@ ensures true;
struct foo test5()
{
    test4((struct foo){20, 30});
    return (struct foo){40, 50};
}

//@ requires true;
//@ ensures true;
struct foo test6()
{
    test4((struct foo){.y = 30, .x = 20});
    return (struct foo){.y = 50, .x = 40};
}