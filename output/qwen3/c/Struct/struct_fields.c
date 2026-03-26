#include <assert.h>
#include <stdint.h>
#include <stddef.h>

struct foo
{
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

/*@ predicate foo_inv(struct foo *f) =
    f->x |-> ?x &*&
    f->y |-> ?y &*&
    f->c |-> ?c &*&
    f->uc |-> ?uc &*&
    f->s |-> ?s &*&
    f->us |-> ?us &*&
    f->u |-> ?u &*&
    f->l |-> ?l &*&
    f->ul |-> ?ul &*&
    f->ll |-> ?ll &*&
    f->ull |-> ?ull &*&
    f->i32 |-> ?i32 &*&
    f->u32 |-> ?u32 &*&
    f->i128 |-> ?i128 &*&
    f->u128 |-> ?u128 &*&
    f->p |-> ?p &*&
    f->ip |-> ?ip &*&
    f->up |-> ?up;
@*/

int main()
{
    struct foo f;
    //@ assume foo_inv(&f);
    
    (&f)->x = 4;
    //@ assert foo_inv(&f) &*& f.x == 4;
    
    int i = f.x;
    //@ assert foo_inv(&f) &*& i == 4;
    
    f.x = 5;
    //@ assert foo_inv(&f) &*& f.x == 5;
    
    int j = (&f)->x;
    //@ assert foo_inv(&f) &*& j == 5;
    
    int temp = f.x;
    //@ assert foo_inv(&f) &*& temp == 5;
    
    f.x = 7;
    f.y = 8;
    //@ assert foo_inv(&f) &*& f.x == 7 &*& f.y == 8;
    
    f.c = 42;
    char *pc = &f.c;
    //@ assume pc == &f.c;
    (*pc)++;
    //@ assert foo_inv(&f) &*& f.c == 43;
    char c = f.c;
    //@ assert c == 43;
    assert(c == 43);
    
    f.uc = 42;
    unsigned char *puc = &f.uc;
    //@ assume puc == &f.uc;
    (*puc)++;
    //@ assert foo_inv(&f) &*& f.uc == 43;
    unsigned char uc = f.uc;
    //@ assert uc == 43;
    assert(uc == 43);
    
    f.s = 42;
    short *ps = &f.s;
    //@ assume ps == &f.s;
    (*ps)++;
    //@ assert foo_inv(&f) &*& f.s == 43;
    short s = f.s;
    //@ assert s == 43;
    assert(s == 43);
    
    f.us = 42;
    unsigned short *pus = &f.us;
    //@ assume pus == &f.us;
    *pus = (unsigned short)((unsigned)*pus + 1);
    //@ assert foo_inv(&f) &*& f.us == 43;
    unsigned short us = f.us;
    //@ assert us == 43;
    
    f.x = 42;
    int *pi = &f.x;
    //@ assume pi == &f.x;
    (*pi)++;
    //@ assert foo_inv(&f) &*& f.x == 43;
    int x = f.x;
    //@ assert x == 43;
    assert(x == 43);
    
    f.u = 42;
    unsigned *pu = &f.u;
    //@ assume pu == &f.u;
    (*pu)++;
    //@ assert foo_inv(&f) &*& f.u == 43;
    unsigned u = f.u;
    //@ assert u == 43;
    assert(u == 43);
    
    f.l = 42;
    long *pl = &f.l;
    //@ assume pl == &f.l;
    (*pl)++;
    //@ assert foo_inv(&f) &*& f.l == 43;
    long l = f.l;
    //@ assert l == 43;
    assert(l == 43);
    
    f.ul = 42;
    unsigned long *pul = &f.ul;
    //@ assume pul == &f.ul;
    (*pul)++;
    //@ assert foo_inv(&f) &*& f.ul == 43;
    unsigned long ul = f.ul;
    //@ assert ul == 43;
    assert(ul == 43);
    
    f.ll = 42;
    long long *pll = &f.ll;
    //@ assume pll == &f.ll;
    (*pll)++;
    //@ assert foo_inv(&f) &*& f.ll == 43;
    long long ll = f.ll;
    //@ assert ll == 43;
    assert(ll == 43);
    
    f.ull = 42;
    unsigned long long *pull = &f.ull;
    //@ assume pull == &f.ull;
    (*pull)++;
    //@ assert foo_inv(&f) &*& f.ull == 43;
    unsigned long long ull = f.ull;
    //@ assert ull == 43;
    assert(ull == 43);
    
    f.i32 = 42;
    __int32 *pi32 = &f.i32;
    //@ assume pi32 == &f.i32;
    (*pi32)++;
    //@ assert foo_inv(&f) &*& f.i32 == 43;
    __int32 i32 = f.i32;
    //@ assert i32 == 43;
    assert(i32 == 43);
    
    f.u32 = 42;
    unsigned __int32 *pu32 = &f.u32;
    //@ assume pu32 == &f.u32;
    (*pu32)++;
    //@ assert foo_inv(&f) &*& f.u32 == 43;
    unsigned __int32 u32 = f.u32;
    //@ assert u32 == 43;
    assert(u32 == 43);
    
    f.i128 = 42;
    __int128 *pi128 = &f.i128;
    //@ assume pi128 == &f.i128;
    (*pi128)++;
    //@ assert foo_inv(&f) &*& f.i128 == 43;
    __int128 i128 = f.i128;
    //@ assert i128 == 43;
    assert(i128 == 43);
    
    f.u128 = 42;
    unsigned __int128 *pu128 = &f.u128;
    //@ assume pu128 == &f.u128;
    (*pu128)++;
    //@ assert foo_inv(&f) &*& f.u128 == 43;
    unsigned __int128 u128 = f.u128;
    //@ assert u128 == 43;
    assert(u128 == 43);
    
    f.p = (void *)42;
    void **pp = &f.p;
    //@ assume pp == &f.p;
    *pp = (void *)((uintptr_t)*pp + 1);
    //@ assert foo_inv(&f) &*& f.p == (void *)43;
    void *p = f.p;
    //@ assert p == (void *)43;
    assert(p == (void *)43);
    
    f.ip = 42;
    intptr_t *pip = &f.ip;
    //@ assume pip == &f.ip;
    (*pip)++;
    //@ assert foo_inv(&f) &*& f.ip == 43;
    intptr_t ip = f.ip;
    //@ assert ip == 43;
    assert(ip == 43);
    
    f.up = 42;
    uintptr_t *pup = &f.up;
    //@ assume pup == &f.up;
    (*pup)++;
    //@ assert foo_inv(&f) &*& f.up == 43;
    uintptr_t up = f.up;
    //@ assert up == 43;
    assert(up == 43);
    
    return 0;
}