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
predicate foo_pred(struct foo *f) = f->x |-> _ &*& f->y |-> _ &*& f->c |-> _ &*& f->uc |-> _ &*&
    f->s |-> _ &*& f->us |-> _ &*& f->u |-> _ &*& f->l |-> _ &*& f->ul |-> _ &*&
    f->ll |-> _ &*& f->ull |-> _ &*& f->i32 |-> _ &*& f->u32 |-> _ &*& f->i128 |-> _ &*& f->u128 |-> _ &*&
    f->p |-> _ &*& f->ip |-> _ &*& f->up |-> _;
@*/

int main() 
    //@ requires true;
    //@ ensures true;
{
    struct foo f;
    //@ close foo_pred(&f);

    (&f)->x = 4;
   
    int i = f.x;
    
    f.x = 5;
    int j = (&f)->x;
    
    //@ open foo_pred(&f);
    int temp = f.x;
    //@ close foo_pred(&f);

    //@ open foo_pred(&f);
    f.x = 7;
    f.y = 8;
    //@ close foo_pred(&f);

    //@ open foo_pred(&f);
    f.c = 42;
    //@ close foo_pred(&f);
    char *pc = &f.c;
    //@ open foo_pred(&f);
    (*pc)++;
    //@ close foo_pred(&f);
    char c = f.c;
    assert(c == 43);
    
    //@ open foo_pred(&f);
    f.uc = 42;
    //@ close foo_pred(&f);
    unsigned char *puc = &f.uc;
    //@ open foo_pred(&f);
    (*puc)++;
    //@ close foo_pred(&f);
    unsigned char uc = f.uc;
    assert(uc == 43);
    
    //@ open foo_pred(&f);
    f.s = 42;
    //@ close foo_pred(&f);
    short *ps = &f.s;
    //@ open foo_pred(&f);
    (*ps)++;
    //@ close foo_pred(&f);
    short s = f.s;
    assert(s == 43);
    
    //@ open foo_pred(&f);
    f.us = 42;
    //@ close foo_pred(&f);
    unsigned short *pus = &f.us;
    //@ open foo_pred(&f);
    *pus = (unsigned short)((unsigned)*pus + 1);
    //@ close foo_pred(&f);
    unsigned short us = f.us;
    
    //@ open foo_pred(&f);
    f.x = 42;
    //@ close foo_pred(&f);
    int *pi = &f.x;
    //@ open foo_pred(&f);
    (*pi)++;
    //@ close foo_pred(&f);
    int x = f.x;
    assert(x == 43);
    
    //@ open foo_pred(&f);
    f.u = 42;
    //@ close foo_pred(&f);
    unsigned *pu = &f.u;
    //@ open foo_pred(&f);
    (*pu)++;
    //@ close foo_pred(&f);
    unsigned u = f.u;
    assert(u == 43);
    
    //@ open foo_pred(&f);
    f.l = 42;
    //@ close foo_pred(&f);
    long *pl = &f.l;
    //@ open foo_pred(&f);
    (*pl)++;
    //@ close foo_pred(&f);
    long l = f.l;
    assert(l == 43);
    
    //@ open foo_pred(&f);
    f.ul = 42;
    //@ close foo_pred(&f);
    unsigned long *pul = &f.ul;
    //@ open foo_pred(&f);
    (*pul)++;
    //@ close foo_pred(&f);
    unsigned long ul = f.ul;
    assert(ul == 43);
    
    //@ open foo_pred(&f);
    f.ll = 42;
    //@ close foo_pred(&f);
    long long *pll = &f.ll;
    //@ open foo_pred(&f);
    (*pll)++;
    //@ close foo_pred(&f);
    long long ll = f.ll;
    assert(ll == 43);

    //@ open foo_pred(&f);
    f.ull = 42;
    //@ close foo_pred(&f);
    unsigned long long *pull = &f.ull;
    //@ open foo_pred(&f);
    (*pull)++;
    //@ close foo_pred(&f);
    unsigned long long ull = f.ull;
    assert(ull == 43);
    
    //@ open foo_pred(&f);
    f.i32 = 42;
    //@ close foo_pred(&f);
    __int32 *pi32 = &f.i32;
    //@ open foo_pred(&f);
    (*pi32)++;
    //@ close foo_pred(&f);
    __int32 i32 = f.i32;
    assert(i32 == 43);
    
    //@ open foo_pred(&f);
    f.u32 = 42;
    //@ close foo_pred(&f);
    unsigned __int32 *pu32 = &f.u32;
    //@ open foo_pred(&f);
    (*pu32)++;
    //@ close foo_pred(&f);
    unsigned __int32 u32 = f.u32;
    assert(u32 == 43);
    
    //@ open foo_pred(&f);
    f.i128 = 42;
    //@ close foo_pred(&f);
    __int128 *pi128 = &f.i128;
    //@ open foo_pred(&f);
    (*pi128)++;
    //@ close foo_pred(&f);
    __int128 i128 = f.i128;
    assert(i128 == 43);
    
    //@ open foo_pred(&f);
    f.u128 = 42;
    //@ close foo_pred(&f);
    unsigned __int128 *pu128 = &f.u128;
    //@ open foo_pred(&f);
    (*pu128)++;
    //@ close foo_pred(&f);
    unsigned __int128 u128 = f.u128;
    assert(u128 == 43);
    
    //@ open foo_pred(&f);
    f.p = (void *)42;
    //@ close foo_pred(&f);
    void **pp = &f.p;
    //@ open foo_pred(&f);
    *pp = (void *)((uintptr_t)*pp + 1);
    //@ close foo_pred(&f);
    void *p = f.p;
    assert(p == (void *)43);
    
    //@ open foo_pred(&f);
    f.ip = 42;
    //@ close foo_pred(&f);
    intptr_t *pip = &f.ip;
    //@ open foo_pred(&f);
    (*pip)++;
    //@ close foo_pred(&f);
    intptr_t ip = f.ip;
    assert(ip == 43);
    
    //@ open foo_pred(&f);
    f.up = 42;
    //@ close foo_pred(&f);
    uintptr_t *pup = &f.up;
    //@ open foo_pred(&f);
    (*pup)++;
    //@ close foo_pred(&f);
    uintptr_t up = f.up;
    assert(up == 43);
    
    //@ open foo_pred(&f);
    return 0;
}