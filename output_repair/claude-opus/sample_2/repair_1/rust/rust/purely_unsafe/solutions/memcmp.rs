use std::alloc::{alloc, dealloc, Layout};

/*@

pred u8s(p: *u8, count: usize; vs: list<u8>) =
    if count == 0 {
        vs == nil
    } else {
        *p |-> ?v &*& u8s(p.add(1), count - 1, ?vs_tail) &*& vs == cons(v, vs_tail)
    };

lem u8s_split(p: *u8, count: usize, i: usize)
    req u8s(p, count, ?vs) &*& 0 <= i &*& i <= count;ens u8s(p, i, take(i as i32, vs)) &*& u8s(p.add(i), count - i, drop(i as i32, vs));
{
    if i == 0 {
    } else {
        open u8s(p, count, vs);
        u8s_split(p.add(1), count - 1, i - 1);
        close u8s(p, i, take(i as i32, vs));
    }
}

lem u8s_join(p: *u8, i: usize)
    req u8s(p, i, ?vs1) &*& u8s(p.add(i), ?count2, ?vs2);
    ens u8s(p, i + count2, append(vs1, vs2));
{
    if i == 0 {
        open u8s(p, 0, vs1);
    } else {
        open u8s(p, i, vs1);
        u8s_join(p.add(1), i - 1);
        close u8s(p, i + count2, append(vs1, vs2));
    }
}

@*/

unsafe fn memcmp(p1: *const u8, p2: *const u8, count: usize) -> i32
//@ req u8s(p1 as *u8, count, ?vs1) &*& u8s(p2 as *u8, count, ?vs2);
//@ ens u8s(p1 as *u8, count, vs1) &*& u8s(p2 as *u8, count, vs2);
{
    let mut result = 0;
    let mut i = 0;
    loop
    //@ inv u8s(p1 as *u8, i, take(i as i32, vs1)) &*& u8s((p1 as *u8).add(i), count - i, drop(i as i32, vs1)) &*& u8s(p2 as *u8, i, take(i as i32, vs2)) &*& u8s((p2 as *u8).add(i), count - i, drop(i as i32, vs2)) &*& 0 <= i &*& i <= count;
    {
        if i == count {
            break;
        }
        //@ open u8s((p1 as *u8).add(i), count - i, drop(i as i32, vs1));
        //@ open u8s((p2 as *u8).add(i), count - i, drop(i as i32, vs2));
        let v1 = *p1.add(i);
        let v2 = *p2.add(i);
        //@ close u8s((p1 as *u8).add(i), 1, cons(v1, nil));
        //@ close u8s((p2 as *u8).add(i), 1, cons(v2, nil));
        //@ u8s_join(p1 as *u8, i);
        //@ u8s_join(p2 as *u8, i);
        //@ u8s_split(p1 as *u8, i + 1, i + 1);
        //@ u8s_split(p2 as *u8, i + 1, i + 1);
        if v1 < v2 {
            result = -1;
            //@ u8s_join(p1 as *u8, i + 1);
            //@ u8s_join(p2 as *u8, i + 1);
            break;
        }
        if v1 > v2 {
            result = 1;
            //@ u8s_join(p1 as *u8, i + 1);
            //@ u8s_join(p2 as *u8, i + 1);
            break;
        }
        i += 1;
    }
    //@ u8s_join(p1 as *u8, i);
    //@ u8s_join(p2 as *u8, i);
    result
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}