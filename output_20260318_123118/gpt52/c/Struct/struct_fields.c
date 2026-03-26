#include <stdint.h>
#include <assert.h>

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

predicate foo_x(struct foo *f; int x) = f->x |-> x;
predicate foo_y(struct foo *f; int y) = f->y |-> y;
predicate foo_c(struct foo *f; char c) = f->c |-> c;
predicate foo_uc(struct foo *f; unsigned char uc) = f->uc |-> uc;
predicate foo_s(struct foo *f; short s) = f->s |-> s;
predicate foo_us(struct foo *f; unsigned short us) = f->us |-> us;
predicate foo_u(struct foo *f; unsigned u) = f->u |-> u;
predicate foo_l(struct foo *f; long l) = f->l |-> l;
predicate foo_ul(struct foo *f; unsigned long ul) = f->ul |-> ul;
predicate foo_ll(struct foo *f; long long ll) = f->ll |-> ll;
predicate foo_ull(struct foo *f; unsigned long long ull) = f->ull |-> ull;
predicate foo_i32(struct foo *f; __int32 i32) = f->i32 |-> i32;
predicate foo_u32(struct foo *f; unsigned __int32 u32) = f->u32 |-> u32;
predicate foo_i128(struct foo *f; __int128 i128) = f->i128 |-> i128;
predicate foo_u128(struct foo *f; unsigned __int128 u128) = f->u128 |-> u128;
predicate foo_p(struct foo *f; void *p) = f->p |-> p;
predicate foo_ip(struct foo *f; intptr_t ip) = f->ip |-> ip;
predicate foo_up(struct foo *f; uintptr_t up) = f->up |-> up;

@*/

int main() 
    //@ requires true;
    //@ ensures true;
    
    
{
    struct foo f;
        
    //@ close foo_x(&f, _);
    (&f)->x = 4;
    //@ open foo_x(&f, _);
    //@ close foo_x(&f, 4);
   
    //@ open foo_x(&f, 4);
    int i = f.x;
    //@ close foo_x(&f, 4);
    
    
    //@ open foo_x(&f, 4);
    f.x = 5;
    //@ close foo_x(&f, 5);
    //@ open foo_x(&f, 5);
    int j = (&f)->x;
    //@ close foo_x(&f, 5);
    
    
    //@ open foo_x(&f, 5);
    int temp = f.x;
    //@ close foo_x(&f, 5);
    
    
    //@ open foo_x(&f, 5);
    f.x = 7;
    //@ close foo_x(&f, 7);
    //@ close foo_y(&f, _);
    f.y = 8;
    //@ open foo_y(&f, _);
    //@ close foo_y(&f, 8);
    
    
    
    //@ close foo_c(&f, _);
    f.c = 42;
    //@ open foo_c(&f, _);
    char *pc = &f.c;
    (*pc)++;
    //@ close foo_c(&f, 43);
    //@ open foo_c(&f, 43);
    char c = f.c;
    //@ close foo_c(&f, 43);
    assert(c == 43);
    
    //@ close foo_uc(&f, _);
    f.uc = 42;
    //@ open foo_uc(&f, _);
    unsigned char *puc = &f.uc;
    (*puc)++;
    //@ close foo_uc(&f, 43);
    //@ open foo_uc(&f, 43);
    unsigned char uc = f.uc;
    //@ close foo_uc(&f, 43);
    assert(uc == 43);
    
    //@ close foo_s(&f, _);
    f.s = 42;
    //@ open foo_s(&f, _);
    short *ps = &f.s;
    (*ps)++;
    //@ close foo_s(&f, 43);
    //@ open foo_s(&f, 43);
    short s = f.s;
    //@ close foo_s(&f, 43);
    assert(s == 43);
    
    //@ close foo_us(&f, _);
    f.us = 42;
    //@ open foo_us(&f, _);
    unsigned short *pus = &f.us;
    *pus = (unsigned short)((unsigned)*pus + 1);
    //@ close foo_us(&f, 43);
    //@ open foo_us(&f, 43);
    unsigned short us = f.us;
    //@ close foo_us(&f, 43);
    
    //@ open foo_x(&f, 7);
    f.x = 42;
    //@ close foo_x(&f, 42);
    //@ open foo_x(&f, 42);
    int *pi = &f.x;
    (*pi)++;
    //@ close foo_x(&f, 43);
    //@ open foo_x(&f, 43);
    int x = f.x;
    //@ close foo_x(&f, 43);
    assert(x == 43);
    
    //@ close foo_u(&f, _);
    f.u = 42;
    //@ open foo_u(&f, _);
    unsigned *pu = &f.u;
    (*pu)++;
    //@ close foo_u(&f, 43);
    //@ open foo_u(&f, 43);
    unsigned u = f.u;
    //@ close foo_u(&f, 43);
    assert(u == 43);
    
    //@ close foo_l(&f, _);
    f.l = 42;
    //@ open foo_l(&f, _);
    long *pl = &f.l;
    (*pl)++;
    //@ close foo_l(&f, 43);
    //@ open foo_l(&f, 43);
    long l = f.l;
    //@ close foo_l(&f, 43);
    assert(l == 43);
    
    //@ close foo_ul(&f, _);
    f.ul = 42;
    //@ open foo_ul(&f, _);
    unsigned long *pul = &f.ul;
    (*pul)++;
    //@ close foo_ul(&f, 43);
    //@ open foo_ul(&f, 43);
    unsigned long ul = f.ul;
    //@ close foo_ul(&f, 43);
    assert(ul == 43);
    
    //@ close foo_ll(&f, _);
    f.ll = 42;
    //@ open foo_ll(&f, _);
    long long *pll = &f.ll;
    (*pll)++;
    //@ close foo_ll(&f, 43);
    //@ open foo_ll(&f, 43);
    long long ll = f.ll;
    //@ close foo_ll(&f, 43);
    assert(ll == 43);

    //@ close foo_ull(&f, _);
    f.ull = 42;
    //@ open foo_ull(&f, _);
    unsigned long long *pull = &f.ull;
    (*pull)++;
    //@ close foo_ull(&f, 43);
    //@ open foo_ull(&f, 43);
    unsigned long long ull = f.ull;
    //@ close foo_ull(&f, 43);
    assert(ull == 43);
    
    //@ close foo_i32(&f, _);
    f.i32 = 42;
    //@ open foo_i32(&f, _);
    __int32 *pi32 = &f.i32;
    (*pi32)++;
    //@ close foo_i32(&f, 43);
    //@ open foo_i32(&f, 43);
    __int32 i32 = f.i32;
    //@ close foo_i32(&f, 43);
    assert(i32 == 43);
    
    //@ close foo_u32(&f, _);
    f.u32 = 42;
    //@ open foo_u32(&f, _);
    unsigned __int32 *pu32 = &f.u32;
    (*pu32)++;
    //@ close foo_u32(&f, 43);
    //@ open foo_u32(&f, 43);
    unsigned __int32 u32 = f.u32;
    //@ close foo_u32(&f, 43);
    assert(u32 == 43);
    
    //@ close foo_i128(&f, _);
    f.i128 = 42;
    //@ open foo_i128(&f, _);
    __int128 *pi128 = &f.i128;
    (*pi128)++;
    //@ close foo_i128(&f, 43);
    //@ open foo_i128(&f, 43);
    __int128 i128 = f.i128;
    //@ close foo_i128(&f, 43);
    assert(i128 == 43);
    
    //@ close foo_u128(&f, _);
    f.u128 = 42;
    //@ open foo_u128(&f, _);
    unsigned __int128 *pu128 = &f.u128;
    (*pu128)++;
    //@ close foo_u128(&f, 43);
    //@ open foo_u128(&f, 43);
    unsigned __int128 u128 = f.u128;
    //@ close foo_u128(&f, 43);
    assert(u128 == 43);
    
    //@ close foo_p(&f, _);
    f.p = (void *)42;
    //@ open foo_p(&f, _);
    void **pp = &f.p;
    *pp = (void *)((uintptr_t)*pp + 1);
    //@ close foo_p(&f, (void *)43);
    //@ open foo_p(&f, (void *)43);
    void *p = f.p;
    //@ close foo_p(&f, (void *)43);
    assert(p == (void *)43);
    
    //@ close foo_ip(&f, _);
    f.ip = 42;
    //@ open foo_ip(&f, _);
    intptr_t *pip = &f.ip;
    (*pip)++;
    //@ close foo_ip(&f, 43);
    //@ open foo_ip(&f, 43);
    intptr_t ip = f.ip;
    //@ close foo_ip(&f, 43);
    assert(ip == 43);
    
    //@ close foo_up(&f, _);
    f.up = 42;
    //@ open foo_up(&f, _);
    uintptr_t *pup = &f.up;
    (*pup)++;
    //@ close foo_up(&f, 43);
    //@ open foo_up(&f, 43);
    uintptr_t up = f.up;
    //@ close foo_up(&f, 43);
    assert(up == 43);
    
    return 0;
}