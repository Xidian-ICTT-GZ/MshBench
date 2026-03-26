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

/*@
predicate foo_fields(struct foo *f) =
    f->x |-> ?x_val &*&
    f->y |-> ?y_val &*&
    f->c |-> ?c_val &*&
    f->uc |-> ?uc_val &*&
    f->s |-> ?s_val &*&
    f->us |-> ?us_val &*&
    f->u |-> ?u_val &*&
    f->l |-> ?l_val &*&
    f->ul |-> ?ul_val &*&
    f->ll |-> ?ll_val &*&
    f->ull |-> ?ull_val &*&
    f->i32 |-> ?i32_val &*&
    f->u32 |-> ?u32_val &*&
    f->i128 |-> ?i128_val &*&
    f->u128 |-> ?u128_val &*&
    f->p |-> ?p_val &*&
    f->ip |-> ?ip_val &*&
    f->up |-> ?up_val;
@*/

int main() 
    //@ requires true;
    //@ ensures true;
{
    struct foo f;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    (&f)->x = 4;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    int i = f.x;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.x = 5;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    int j = (&f)->x;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    int temp = f.x;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.x = 7;
    f.y = 8;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.c = 42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    char *pc = &f.c;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    (*pc)++;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    char c = f.c;
    assert(c == 43);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.uc = 42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    unsigned char *puc = &f.uc;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    (*puc)++;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    unsigned char uc = f.uc;
    assert(uc == 43);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.s = 42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    short *ps = &f.s;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    (*ps)++;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    short s = f.s;
    assert(s == 43);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.us = 42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    unsigned short *pus = &f.us;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    *pus = (unsigned short)((unsigned)*pus + 1);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    unsigned short us = f.us;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.x = 42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    int *pi = &f.x;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    (*pi)++;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    int x = f.x;
    assert(x == 43);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.u = 42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    unsigned *pu = &f.u;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    (*pu)++;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    unsigned u = f.u;
    assert(u == 43);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.l = 42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    long *pl = &f.l;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    (*pl)++;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    long l = f.l;
    assert(l == 43);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.ul = 42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    unsigned long *pul = &f.ul;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    (*pul)++;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    unsigned long ul = f.ul;
    assert(ul == 43);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.ll = 42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    long long *pll = &f.ll;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    (*pll)++;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    long long ll = f.ll;
    assert(ll == 43);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.ull = 42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    unsigned long long *pull = &f.ull;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    (*pull)++;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    unsigned long long ull = f.ull;
    assert(ull == 43);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.i32 = 42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    __int32 *pi32 = &f.i32;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    (*pi32)++;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    __int32 i32 = f.i32;
    assert(i32 == 43);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.u32 = 42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    unsigned __int32 *pu32 = &f.u32;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    (*pu32)++;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    unsigned __int32 u32 = f.u32;
    assert(u32 == 43);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.i128 = 42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    __int128 *pi128 = &f.i128;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    (*pi128)++;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    __int128 i128 = f.i128;
    assert(i128 == 43);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.u128 = 42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    unsigned __int128 *pu128 = &f.u128;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    (*pu128)++;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    unsigned __int128 u128 = f.u128;
    assert(u128 == 43);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.p = (void *)42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    void **pp = &f.p;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    *pp = (void *)((uintptr_t)*pp + 1);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    void *p = f.p;
    assert(p == (void *)43);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.ip = 42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    intptr_t *pip = &f.ip;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    (*pip)++;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    intptr_t ip = f.ip;
    assert(ip == 43);
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    f.up = 42;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    uintptr_t *pup = &f.up;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    (*pup)++;
    //@ close foo_fields(&f);

    //@ open foo_fields(&f);
    uintptr_t up = f.up;
    assert(up == 43);
    //@ close foo_fields(&f);

    return 0;
}