struct foo {
    int x;
    int y;
};

/*@ predicate foo(struct foo* p; int x, int y) =
    p->x |-> x &*& p->y |-> y;
@*/

struct bar {
    struct foo p;
    struct foo q;
};

/*@ predicate bar(struct bar* p; struct foo px, struct foo py) =
    foo(&p->p; px.x, px.y) &*& foo(&p->q; py.x, py.y);
@*/

void test()
{
    struct foo a = {1, 2};
    struct foo b = {3, 4};

    struct bar r = {{5, 6}, {7, 8}};
    struct bar t;

    //@ close foo(&t.p; 0, 0);
    //@ close foo(&t.q; 0, 0);
    //@ close bar(&t; (struct foo){0,0}, (struct foo){0,0});
    t.p.x = 10;
    t.p.y = 20;
    t.q.x = 30;
    t.q.y = 40;
    //@ open bar(&t; ?px, ?py);
    //@ close foo(&t.p; 10, 20);
    //@ close foo(&t.q; 30, 40);
    //@ close bar(&t; (struct foo){10,20}, (struct foo){30,40});

    //@ open foo(&a; ?ax, ?ay);
    //@ close foo(&a; 3, 4);
    a = b;

    //@ open bar(&r; ?rx, ?ry);
    //@ open foo(&r.p; ?px, ?py);
    //@ open foo(&r.q; ?qx, ?qy);
    //@ close foo(&r.p; qx, qy);
    //@ close bar(&r; (struct foo){qx,qy}, (struct foo){qx,qy});
    r.p = r.q;

    //@ open bar(&r; ?rx, ?ry);
    //@ open foo(&r.q; ?qx, ?qy);
    //@ open foo(&t.p; ?tx, ?ty);
    //@ close foo(&r.q; tx, ty);
    //@ close bar(&r; ?rx, (struct foo){tx,ty});
    r.q = t.p;

    //@ open foo(&a; ?ax, ?ay);
    //@ open bar(&r; ?rx, ?ry);
    //@ open foo(&r.p; ?px, ?py);
    //@ close foo(&a; px, py);
    a = r.p;

    //@ open foo(&t.p; ?tx, ?ty);
    //@ open foo(&b; ?bx, ?by);
    //@ close foo(&t.p; bx, by);
    t.p = b;

    //@ open bar(&r; ?rx, ?ry);
    //@ open bar(&t; ?tx, ?ty);
    //@ close bar(&r; tx, ty);
    r = t;
}

void test2()
{
    struct foo a = {1, 2};
    struct foo b = {3, 4};

    struct bar r;
    struct bar t;

    //@ close foo(&r.q; 1, 2);
    //@ close foo(&r.p; 0, 0);
    //@ close bar(&r; (struct foo){0,0}, (struct foo){1,2});
    r.q = a;

    //@ close foo(&t.p; 3, 4);
    //@ close foo(&t.q; 0, 0);
    //@ close bar(&t; (struct foo){3,4}, (struct foo){0,0});
    t.p = b;

    //@ open foo(&a; ?ax, ?ay);
    //@ close foo(&a; 3, 4);
    a = b;

    //@ open bar(&r; ?rx, ?ry);
    //@ open foo(&r.p; ?px, ?py);
    //@ open foo(&r.q; ?qx, ?qy);
    //@ close foo(&r.p; qx, qy);
    //@ close bar(&r; (struct foo){qx,qy}, (struct foo){qx,qy});
    r.p = r.q;

    //@ open bar(&r; ?rx, ?ry);
    //@ open foo(&r.q; ?qx, ?qy);
    //@ open foo(&t.p; ?tx, ?ty);
    //@ close foo(&r.q; tx, ty);
    //@ close bar(&r; ?rx, (struct foo){tx,ty});
    r.q = t.p;

    //@ open foo(&a; ?ax, ?ay);
    //@ open bar(&r; ?rx, ?ry);
    //@ open foo(&r.p; ?px, ?py);
    //@ close foo(&a; px, py);
    a = r.p;

    //@ open foo(&t.q; ?tx, ?ty);
    //@ open foo(&b; ?bx, ?by);
    //@ close foo(&t.q; bx, by);
    t.q = b;

    //@ open bar(&r; ?rx, ?ry);
    //@ open bar(&t; ?tx, ?ty);
    //@ close bar(&r; tx, ty);
    r = t;
}

void test3()
{
    struct foo a = {1, 2};
    struct foo b = {3, 4};

    struct bar r;
    struct bar t;

    //@ close foo(&r.q; 1, 2);
    //@ close foo(&r.p; 0, 0);
    //@ close bar(&r; (struct foo){0,0}, (struct foo){1,2});
    r.q = a;

    //@ close foo(&t.p; 3, 4);
    //@ close foo(&t.q; 1, 2);
    //@ close bar(&t; (struct foo){3,4}, (struct foo){1,2});
    t.p = b;
    t.q = a;

    //@ open foo(&a; ?ax, ?ay);
    //@ close foo(&a; 3, 4);
    a = b;

    //@ open bar(&r; ?rx, ?ry);
    //@ open foo(&r.p; ?px, ?py);
    //@ open foo(&r.q; ?qx, ?qy);
    //@ close foo(&r.p; qx, qy);
    //@ close bar(&r; (struct foo){qx,qy}, (struct foo){qx,qy});
    r.p = r.q;

    //@ open bar(&r; ?rx, ?ry);
    //@ open foo(&r.q; ?qx, ?qy);
    //@ open foo(&t.p; ?tx, ?ty);
    //@ close foo(&r.q; tx, ty);
    //@ close bar(&r; ?rx, (struct foo){tx,ty});
    r.q = t.p;

    //@ open foo(&a; ?ax, ?ay);
    //@ open bar(&r; ?rx, ?ry);
    //@ open foo(&r.p; ?px, ?py);
    //@ close foo(&a; px, py);
    a = r.p;

    //@ open foo(&t.p; ?tx, ?ty);
    //@ open foo(&b; ?bx, ?by);
    //@ close foo(&t.p; bx, by);
    t.p = b;

    //@ open bar(&r; ?rx, ?ry);
    //@ open bar(&t; ?tx, ?ty);
    //@ close bar(&r; tx, ty);
    r = t;
}

void test4(struct foo f)
    //@ requires foo(&f; ?x, ?y);
    //@ ensures foo(&f; x, y);
{
    //@ open foo(&f; ?x, ?y);
    //@ close foo(&f; x, y);
}

struct foo test5()
    //@ requires true;
    //@ ensures foo(result; 40, 50);
{
    test4((struct foo){20, 30});
    return (struct foo){40, 50};
}

struct foo test6()
    //@ requires true;
    //@ ensures foo(result; 40, 50);
{
    test4((struct foo){.y = 30, .x = 20});
    return (struct foo){.y = 50, .x = 40};
}