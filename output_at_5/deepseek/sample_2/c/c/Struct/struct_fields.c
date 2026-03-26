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
predicate foo(struct foo *f;) =
    integer(&f->x, ?x) &*&
    integer(&f->y, ?y) &*&
    character(&f->c, ?c) &*&
    u_character(&f->uc, ?uc) &*&
    short_integer(&f->s, ?s) &*&
    u_short_integer(&f->us, ?us) &*&
    u_integer(&f->u, ?u) &*&
    long_integer(&f->l, ?l) &*&
    u_long_integer(&f->ul, ?ul) &*&
    llong_integer(&f->ll, ?ll) &*&
    u_llong_integer(&f->ull, ?ull) &*&
    integer(&f->i32, ?i32) &*&
    u_integer(&f->u32, ?u32) &*&
    integer128(&f->i128, ?i128) &*&
    u_integer128(&f->u128, ?u128) &*&
    pointer(&f->p, ?p) &*&
    integer(&f->ip, ?ip) &*&
    u_integer(&f->up, ?up);
@*/

int main() 
    //@ requires true;
    //@ ensures true;
{
    struct foo f;
    //@ close foo(&f);
        
    (&f)->x = 4;
    //@ open foo(&f);
    //@ close foo(&f);
   
    int i = f.x;
    //@ open foo(&f);
    //@ close foo(&f);
    
    
    f.x = 5;
    //@ open foo(&f);
    //@ close foo(&f);
    int j = (&f)->x;
    //@ open foo(&f);
    //@ close foo(&f);
    
    
    int temp = f.x;
    //@ open foo(&f);
    //@ close foo(&f);
    
    
    f.x = 7;
    //@ open foo(&f);
    //@ close foo(&f);
    f.y = 8;
    //@ open foo(&f);
    //@ close foo(&f);
    
    
    
    f.c = 42;
    //@ open foo(&f);
    //@ close foo(&f);
    char *pc = &f.c;
    //@ open foo(&f);
    //@ close foo(&f);
    (*pc)++;
    //@ open foo(&f);
    //@ close foo(&f);
    char c = f.c;
    //@ open foo(&f);
    //@ close foo(&f);
    assert(c == 43);
    
    f.uc = 42;
    //@ open foo(&f);
    //@ close foo(&f);
    unsigned char *puc = &f.uc;
    //@ open foo(&f);
    //@ close foo(&f);
    (*puc)++;
    //@ open foo(&f);
    //@ close foo(&f);
    unsigned char uc = f.uc;
    //@ open foo(&f);
    //@ close foo(&f);
    assert(uc == 43);
    
    f.s = 42;
    //@ open foo(&f);
    //@ close foo(&f);
    short *ps = &f.s;
    //@ open foo(&f);
    //@ close foo(&f);
    (*ps)++;
    //@ open foo(&f);
    //@ close foo(&f);
    short s = f.s;
    //@ open foo(&f);
    //@ close foo(&f);
    assert(s == 43);
    
    f.us = 42;
    //@ open foo(&f);
    //@ close foo(&f);
    unsigned short *pus = &f.us;
    //@ open foo(&f);
    //@ close foo(&f);
    *pus = (unsigned short)((unsigned)*pus + 1);
    //@ open foo(&f);
    //@ close foo(&f);
    unsigned short us = f.us;
    //@ open foo(&f);
    //@ close foo(&f);
    
    f.x = 42;
    //@ open foo(&f);
    //@ close foo(&f);
    int *pi = &f.x;
    //@ open foo(&f);
    //@ close foo(&f);
    (*pi)++;
    //@ open foo(&f);
    //@ close foo(&f);
    int x = f.x;
    //@ open foo(&f);
    //@ close foo(&f);
    assert(x == 43);
    
    f.u = 42;
    //@ open foo(&f);
    //@ close foo(&f);
    unsigned *pu = &f.u;
    //@ open foo(&f);
    //@ close foo(&f);
    (*pu)++;
    //@ open foo(&f);
    //@ close foo(&f);
    unsigned u = f.u;
    //@ open foo(&f);
    //@ close foo(&f);
    assert(u == 43);
    
    f.l = 42;
    //@ open foo(&f);
    //@ close foo(&f);
    long *pl = &f.l;
    //@ open foo(&f);
    //@ close foo(&f);
    (*pl)++;
    //@ open foo(&f);
    //@ close foo(&f);
    long l = f.l;
    //@ open foo(&f);
    //@ close foo(&f);
    assert(l == 43);
    
    f.ul = 42;
    //@ open foo(&f);
    //@ close foo(&f);
    unsigned long *pul = &f.ul;
    //@ open foo(&f);
    //@ close foo(&f);
    (*pul)++;
    //@ open foo(&f);
    //@ close foo(&f);
    unsigned long ul = f.ul;
    //@ open foo(&f);
    //@ close foo(&f);
    assert(ul == 43);
    
    f.ll = 42;
    //@ open foo(&f);
    //@ close foo(&f);
    long long *pll = &f.ll;
    //@ open foo(&f);
    //@ close foo(&f);
    (*pll)++;
    //@ open foo(&f);
    //@ close foo(&f);
    long long ll = f.ll;
    //@ open foo(&f);
    //@ close foo(&f);
    assert(ll == 43);

    f.ull = 42;
    //@ open foo(&f);
    //@ close foo(&f);
    unsigned long long *pull = &f.ull;
    //@ open foo(&f);
    //@ close foo(&f);
    (*pull)++;
    //@ open foo(&f);
    //@ close foo(&f);
    unsigned long long ull = f.ull;
    //@ open foo(&f);
    //@ close foo(&f);
    assert(ull == 43);
    
    f.i32 = 42;
    //@ open foo(&f);
    //@ close foo(&f);
    __int32 *pi32 = &f.i32;
    //@ open foo(&f);
    //@ close foo(&f);
    (*pi32)++;
    //@ open foo(&f);
    //@ close foo(&f);
    __int32 i32 = f.i32;
    //@ open foo(&f);
    //@ close foo(&f);
    assert(i32 == 43);
    
    f.u32 = 42;
    //@ open foo(&f);
    //@ close foo(&f);
    unsigned __int32 *pu32 = &f.u32;
    //@ open foo(&f);
    //@ close foo(&f);
    (*pu32)++;
    //@ open foo(&f);
    //@ close foo(&f);
    unsigned __int32 u32 = f.u32;
    //@ open foo(&f);
    //@ close foo(&f);
    assert(u32 == 43);
    
    f.i128 = 42;
    //@ open foo(&f);
    //@ close foo(&f);
    __int128 *pi128 = &f.i128;
    //@ open foo(&f);
    //@ close foo(&f);
    (*pi128)++;
    //@ open foo(&f);
    //@ close foo(&f);
    __int128 i128 = f.i128;
    //@ open foo(&f);
    //@ close foo(&f);
    assert(i128 == 43);
    
    f.u128 = 42;
    //@ open foo(&f);
    //@ close foo(&f);
    unsigned __int128 *pu128 = &f.u128;
    //@ open foo(&f);
    //@ close foo(&f);
    (*pu128)++;
    //@ open foo(&f);
    //@ close foo(&f);
    unsigned __int128 u128 = f.u128;
    //@ open foo(&f);
    //@ close foo(&f);
    assert(u128 == 43);
    
    f.p = (void *)42;
    //@ open foo(&f);
    //@ close foo(&f);
    void **pp = &f.p;
    //@ open foo(&f);
    //@ close foo(&f);
    *pp = (void *)((uintptr_t)*pp + 1);
    //@ open foo(&f);
    //@ close foo(&f);
    void *p = f.p;
    //@ open foo(&f);
    //@ close foo(&f);
    assert(p == (void *)43);
    
    f.ip = 42;
    //@ open foo(&f);
    //@ close foo(&f);
    intptr_t *pip = &f.ip;
    //@ open foo(&f);
    //@ close foo(&f);
    (*pip)++;
    //@ open foo(&f);
    //@ close foo(&f);
    intptr_t ip = f.ip;
    //@ open foo(&f);
    //@ close foo(&f);
    assert(ip == 43);
    
    f.up = 42;
    //@ open foo(&f);
    //@ close foo(&f);
    uintptr_t *pup = &f.up;
    //@ open foo(&f);
    //@ close foo(&f);
    (*pup)++;
    //@ open foo(&f);
    //@ close foo(&f);
    uintptr_t up = f.up;
    //@ open foo(&f);
    //@ close foo(&f);
    assert(up == 43);
    
    //@ open foo(&f);
    return 0;
}