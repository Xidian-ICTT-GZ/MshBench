use std::ptr;

/*@

pred u8s(p: *u8, count: usize; vs: list<u8>) =
    if count == 0 {
        vs == nil
    } else {
        *p |-> ?v &*& u8s(ptr_add(p, 1), count - 1, ?vs0) &*& vs == cons(v, vs0)
    };

lem u8s_split(p: *u8, offset: usize)
    req u8s(p, ?count, ?vs) &*& 0 <= offset &*& offset <= count;
    ens u8s(p, offset, take(offset as i32, vs)) &*& u8s(ptr_add(p, offset), count - offset, drop(offset as i32, vs));
{
    if offset == 0 {
    } else {
        open u8s(p, count, vs);
        u8s_split(ptr_add(p, 1), offset - 1);close u8s(p, offset, take(offset as i32, vs));
    }
}

lem u8s_join(p: *u8)
    req u8s(p, ?count1, ?vs1) &*& u8s(ptr_add(p, count1), ?count2, ?vs2);
    ens u8s(p, count1 + count2, append(vs1, vs2));
{
    open u8s(p, count1, vs1);
    if count1 == 0 {
    } else {
        u8s_join(ptr_add(p, 1));
        close u8s(p, count1 + count2, append(vs1, vs2));
    }
}

@*/

unsafe fn memcmp(p1: *const u8, p2: *const u8, count: usize) -> i32
//@ req u8s(p1 as *u8, count, ?vs1) &*& u8s(p2 as *u8, count, ?vs2);
//@ ens u8s(p1 as *u8, count, vs1) &*& u8s(p2 as *u8, count, vs2);
{
    let mut result = 0;
    let mut i: usize = 0;
    loop
    //@ inv u8s(p1 as *u8, count, vs1) &*& u8s(p2 as *u8, count, vs2) &*& 0 <= i &*& i <= count;
    {
        if i == count {
            break;
        }
        //@ u8s_split(p1 as *u8, i);
        //@ u8s_split(p2 as *u8, i);
        //@ open u8s(ptr_add(p1 as *u8, i), count - i, _);
        //@ open u8s(ptr_add(p2 as *u8, i), count - i, _);
        let v1 = *p1.add(i);
        let v2 = *p2.add(i);
        //@ close u8s(ptr_add(p1 as *u8, i), count - i, _);
        //@ close u8s(ptr_add(p2 as *u8, i), count - i, _);
        //@ u8s_join(p1 as *u8);
        //@ u8s_join(p2 as *u8);
        if v1 < v2 {
            result = -1;
            break;
        }
        if v1 > v2 {
            result = 1;
            break;
        }
        i += 1;
    }
    result
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}