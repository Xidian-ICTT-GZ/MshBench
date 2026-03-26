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
    f->x |-> _ &*&
    f->y |-> _ &*&
    f->c |-> _ &*&
    f->uc |-> _ &*&
    f->s |-> _ &*&
    f->us |-> _ &*&
    f->u |-> _ &*&
    f->l |-> _ &*&
    f->ul |-> _ &*&
    f->ll |-> _ &*&
    f->ull |-> _ &*&
    f->i32 |-> _ &*&
    f->u32 |-> _ &*&
    f->i128 |-> _ &*&
    f->u128 |-> _ &*&
    f->p |-> _ &*&
    f->ip |-> _ &*&
    f->up |-> _;
@*/

int main() 
    //@ requires true;
    //@ ensures true;
    
    
{
    struct foo f;
    //@ close foo_fields(&f);
        
    (&f)->x = 4;
   
    int i = f.x;
    
    
    f.x = 5;
    int j = (&f)->x;
    
    
    int temp = f.x;
    
    
    f.x = 7;
    f.y = 8;
    
    
    
    f.c = 42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    char *pc = &f.c;
    (*pc)++;
    char c = f.c;
    assert(c == 43);
    
    f.uc = 42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    unsigned char *puc = &f.uc;
    (*puc)++;
    unsigned char uc = f.uc;
    assert(uc == 43);
    
    f.s = 42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    short *ps = &f.s;
    (*ps)++;
    short s = f.s;
    assert(s == 43);
    
    f.us = 42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    unsigned short *pus = &f.us;
    *pus = (unsigned short)((unsigned)*pus + 1);
    unsigned short us = f.us;
    
    f.x = 42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    int *pi = &f.x;
    (*pi)++;
    int x = f.x;
    assert(x == 43);
    
    f.u = 42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    unsigned *pu = &f.u;
    (*pu)++;
    unsigned u = f.u;
    assert(u == 43);
    
    f.l = 42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    long *pl = &f.l;
    (*pl)++;
    long l = f.l;
    assert(l == 43);
    
    f.ul = 42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    unsigned long *pul = &f.ul;
    (*pul)++;
    unsigned long ul = f.ul;
    assert(ul == 43);
    
    f.ll = 42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    long long *pll = &f.ll;
    (*pll)++;
    long long ll = f.ll;
    assert(ll == 43);

    f.ull = 42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    unsigned long long *pull = &f.ull;
    (*pull)++;
    unsigned long long ull = f.ull;
    assert(ull == 43);
    
    f.i32 = 42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    __int32 *pi32 = &f.i32;
    (*pi32)++;
    __int32 i32 = f.i32;
    assert(i32 == 43);
    
    f.u32 = 42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    unsigned __int32 *pu32 = &f.u32;
    (*pu32)++;
    unsigned __int32 u32 = f.u32;
    assert(u32 == 43);
    
    f.i128 = 42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    __int128 *pi128 = &f.i128;
    (*pi128)++;
    __int128 i128 = f.i128;
    assert(i128 == 43);
    
    f.u128 = 42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    unsigned __int128 *pu128 = &f.u128;
    (*pu128)++;
    unsigned __int128 u128 = f.u128;
    assert(u128 == 43);
    
    f.p = (void *)42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    void **pp = &f.p;
    *pp = (void *)((uintptr_t)*pp + 1);
    void *p = f.p;
    assert(p == (void *)43);
    
    f.ip = 42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    intptr_t *pip = &f.ip;
    (*pip)++;
    intptr_t ip = f.ip;
    assert(ip == 43);
    
    f.up = 42;
    //@ open foo_fields(&f);
    //@ close foo_fields(&f);
    uintptr_t *pup = &f.up;
    (*pup)++;
    uintptr_t up = f.up;
    assert(up == 43);
    
    //@ open foo_fields(&f);
    return 0;
}