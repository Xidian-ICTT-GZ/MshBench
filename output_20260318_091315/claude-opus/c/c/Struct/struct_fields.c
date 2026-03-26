struct foo {
    int x;
    int y;
    char c;
    unsigned char uc;
    short s;
    unsigned short us;
    unsigned u;
    long l;
    unsigned long ul;
    long long ll;
    unsigned long long ull;
    __int32 i32;
    unsigned __int32 u32;
    __int128 i128;
    unsigned __int128 u128;
    void *p;
    intptr_t ip;
    uintptr_t up;
};

/*@ predicate foo(struct foo *f;) =
    f->x |-> ?x
    &*& f->y |-> ?y
    &*& f->c |-> ?c
    &*& f->uc |-> ?uc
    &*& f->s |-> ?s
    &*& f->us |-> ?us
    &*& f->u |-> ?u
    &*& f->l |-> ?l
    &*& f->ul |-> ?ul
    &*& f->ll |-> ?ll
    &*& f->ull |-> ?ull
    &*& f->i32 |-> ?i32
    &*& f->u32 |-> ?u32
    &*& f->i128 |-> ?i128
    &*& f->u128 |-> ?u128
    &*& f->p |-> ?p
    &*& f->ip |-> ?ip
    &*& f->up |-> ?up;
@*/

int main() 
    //@ requires true;
    //@ ensures true;
{
    struct foo f;
    //@ close foo(&f);

    
    //@ open foo(&f);
    f.x = 4;
    int i = f.x;
    //@ close foo(&f);

    //@ open foo(&f);
    f.x = 5;
    int j = f.x;
    //@ close foo(&f);

    //@ open foo(&f);
    int temp = f.x;
    //@ close foo(&f);

    //@ open foo(&f);
    f.x = 7;
    f.y = 8;
    //@ close foo(&f);

    //@ open foo(&f);
    f.c = 42;
    char *pc = &f.c;
    (*pc)++;
    char c = f.c;
    //@ close foo(&f);
    assert(c == 43);

    //@ open foo(&f);
    f.uc = 42;
    unsigned char *puc = &f.uc;
    (*puc)++;
    unsigned char uc = f.uc;
    //@ close foo(&f);
    assert(uc == 43);

    //@ open foo(&f);
    f.s = 42;
    short *ps = &f.s;
    (*ps)++;
    short s = f.s;
    //@ close foo(&f);
    assert(s == 43);

    //@ open foo(&f);
    f.us = 42;
    unsigned short *pus = &f.us;
    *pus = (unsigned short)((unsigned)*pus + 1);
    unsigned short us = f.us;
    //@ close foo(&f);
    

    //@ open foo(&f);
    f.x = 42;
    int *pi = &f.x;
    (*pi)++;
    int x = f.x;
    //@ close foo(&f);
    assert(x == 43);

    //@ open foo(&f);
    f.u = 42;
    unsigned *pu = &f.u;
    (*pu)++;
    unsigned u = f.u;
    //@ close foo(&f);
    assert(u == 43);

    //@ open foo(&f);
    f.l = 42;
    long *pl = &f.l;
    (*pl)++;
    long l = f.l;
    //@ close foo(&f);
    assert(l == 43);

    //@ open foo(&f);
    f.ul = 42;
    unsigned long *pul = &f.ul;
    (*pul)++;
    unsigned long ul = f.ul;
    //@ close foo(&f);
    assert(ul == 43);

    //@ open foo(&f);
    f.ll = 42;
    long long *pll = &f.ll;
    (*pll)++;
    long long ll = f.ll;
    //@ close foo(&f);
    assert(ll == 43);

    //@ open foo(&f);
    f.ull = 42;
    unsigned long long *pull = &f.ull;
    (*pull)++;
    unsigned long long ull = f.ull;
    //@ close foo(&f);
    assert(ull == 43);

    //@ open foo(&f);
    f.i32 = 42;
    __int32 *pi32 = &f.i32;
    (*pi32)++;
    __int32 i32 = f.i32;
    //@ close foo(&f);
    assert(i32 == 43);

    //@ open foo(&f);
    f.u32 = 42;
    unsigned __int32 *pu32 = &f.u32;
    (*pu32)++;
    unsigned __int32 u32 = f.u32;
    //@ close foo(&f);
    assert(u32 == 43);

    //@ open foo(&f);
    f.i128 = 42;
    __int128 *pi128 = &f.i128;
    (*pi128)++;
    __int128 i128 = f.i128;
    //@ close foo(&f);
    assert(i128 == 43);

    //@ open foo(&f);
    f.u128 = 42;
    unsigned __int128 *pu128 = &f.u128;
    (*pu128)++;
    unsigned __int128 u128 = f.u128;
    //@ close foo(&f);
    assert(u128 == 43);

    //@ open foo(&f);
    f.p = (void *)42;
    void **pp = &f.p;
    *pp = (void *)((uintptr_t)*pp + 1);
    void *p = f.p;
    //@ close foo(&f);
    assert(p == (void *)43);

    //@ open foo(&f);
    f.ip = 42;
    intptr_t *pip = &f.ip;
    (*pip)++;
    intptr_t ip = f.ip;
    //@ close foo(&f);
    assert(ip == 43);

    //@ open foo(&f);
    f.up = 42;
    uintptr_t *pup = &f.up;
    (*pup)++;
    uintptr_t up = f.up;
    //@ close foo(&f);
    assert(up == 43);

    return 0;
}