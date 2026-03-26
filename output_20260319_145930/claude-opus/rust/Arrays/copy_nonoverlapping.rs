use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@

pred u8s(ptr: *mut u8, count: usize; vs: list<u8>) =
    if count == 0 {
        vs == nil
    } else {
        *ptr |-> ?v &*& u8s(ptr.add(1), count - 1, ?vs0) &*& vs == cons(v, vs0)
    };

lem_auto u8s_inv()
    req u8s(?ptr, ?count, ?vs);
    ens u8s(ptr, count, vs) &*& length(vs) == count;
{
    open u8s(ptr, count, vs);
    if count != 0 {
        u8s_inv();
    }
    close u8s(ptr, count, vs);
}

pred u8s_const(ptr: *const u8, count: usize; vs: list<u8>) =
    if count == 0 {
        vs == nil
    } else {
        *(ptr as *mut u8) |-> ?v &*& u8s_const((ptr.add(1)), count - 1, ?vs0) &*& vs == cons(v, vs0)
    };

lem_auto u8s_const_inv()
    req u8s_const(?ptr, ?count, ?vs);
    ens u8s_const(ptr, count, vs) &*& length(vs) == count;
{
    open u8s_const(ptr, count, vs);
    if count != 0 {
        u8s_const_inv();
    }
    close u8s_const(ptr, count, vs);
}

lem u8s_const_to_u8s(ptr: *const u8, count: usize)
    req u8s_const(ptr, count, ?vs);
    ens u8s(ptr as *mut u8, count, vs);
{
    open u8s_const(ptr, count, vs);
    if count != 0 {
        u8s_const_to_u8s(ptr.add(1), count - 1);
    }
    close u8s(ptr as *mut u8, count, vs);
}

lem u8s_to_u8s_const(ptr: *mut u8, count: usize)
    req u8s(ptr, count, ?vs);
    ens u8s_const(ptr as *const u8, count, vs);
{
    open u8s(ptr, count, vs);
    if count != 0 {
        u8s_to_u8s_const(ptr.add(1), count - 1);
    }
    close u8s_const(ptr as *const u8, count, vs);
}

lem u8s_split(ptr: *mut u8, offset: usize)
    req u8s(ptr, ?count, ?vs) &*& 0 <= offset &*& offset <= count;
    ens u8s(ptr, offset, take(offset as i32, vs)) &*& u8s(ptr.add(offset), count - offset, drop(offset as i32, vs));
{
    open u8s(ptr, count, vs);
    if offset == 0 {
        close u8s(ptr, 0, nil);
    } else {
        u8s_split(ptr.add(1), offset - 1);
        close u8s(ptr, offset, take(offset as i32, vs));
    }
}

lem u8s_join(ptr: *mut u8)
    req u8s(ptr, ?count1, ?vs1) &*& u8s(ptr.add(count1), ?count2, ?vs2);
    ens u8s(ptr, count1 + count2, append(vs1, vs2));
{
    open u8s(ptr, count1, vs1);
    if count1 == 0 {
    } else {
        u8s_join(ptr.add(1));
        close u8s(ptr, count1 + count2, append(vs1, vs2));
    }
}

lem u8s_const_split(ptr: *const u8, offset: usize)
    req u8s_const(ptr, ?count, ?vs) &*& 0 <= offset &*& offset <= count;
    ens u8s_const(ptr, offset, take(offset as i32, vs)) &*& u8s_const(ptr.add(offset), count - offset, drop(offset as i32, vs));
{
    open u8s_const(ptr, count, vs);
    if offset == 0 {
        close u8s_const(ptr, 0, nil);
    } else {
        u8s_const_split(ptr.add(1), offset - 1);
        close u8s_const(ptr, offset, take(offset as i32, vs));
    }
}

lem u8s_const_join(ptr: *const u8)
    req u8s_const(ptr, ?count1, ?vs1) &*& u8s_const(ptr.add(count1), ?count2, ?vs2);
    ens u8s_const(ptr, count1 + count2, append(vs1, vs2));
{
    open u8s_const(ptr, count1, vs1);
    if count1 == 0 {
    } else {
        u8s_const_join(ptr.add(1));
        close u8s_const(ptr, count1 + count2, append(vs1, vs2));
    }
}

@*/

//@ req u8s_const(src, count, ?vs) &*& u8s(dst, count, _);
//@ ens u8s_const(src, count, vs) &*& u8s(dst, count, vs);
unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
{
    let mut i = 0;
    loop {
        //@ inv u8s_const(src, i, ?copied) &*& u8s_const(src.add(i), count - i, ?remaining) &*& u8s(dst, i, copied) &*& u8s(dst.add(i), count - i, _) &*& i <= count &*& vs == append(copied, remaining);
        if i == count { break; }
        //@ open u8s_const(src.add(i), count - i, remaining);
        //@ open u8s(dst.add(i), count - i, _);
        *dst.add(i) = *src.add(i);
        //@ close u8s_const(src.add(i), 1, cons(head(remaining), nil));
        //@ u8s_const_join(src);
        //@ close u8s(dst.add(i), 1, cons(head(remaining), nil));
        //@ u8s_join(dst);
        i += 1;
    }
    //@ u8s_const_join(src);
    //@ u8s_join(dst);
}

fn main()
{
    unsafe {
        let buffer1: [u8; _] = [10, 20, 30];
        //@ close u8s_const(&raw const buffer1[2] as *const u8, 0, nil);
        //@ close u8s_const(&raw const buffer1[2] as *const u8, 1, cons(30, nil));
        //@ close u8s_const(&raw const buffer1[1] as *const u8, 2, cons(20, cons(30, nil)));
        //@ close u8s_const(&raw const buffer1[0] as *const u8, 3, cons(10, cons(20, cons(30, nil))));
        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        //@ close u8s(buffer2.add(3), 0, nil);
        //@ close u8s(buffer2.add(2), 1, _);
        //@ close u8s(buffer2.add(1), 2, _);
        //@ close u8s(buffer2, 3, _);
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        //@ open u8s(buffer2, 3, _);
        //@ open u8s(buffer2.add(1), 2, _);
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        //@ close u8s(buffer2.add(1), 2, _);
        //@ close u8s(buffer2, 3, _);
        //@ open u8s(buffer2, 3, _);
        //@ open u8s(buffer2.add(1), 2, _);
        //@ open u8s(buffer2.add(2), 1, _);
        //@ open u8s(buffer2.add(3), 0, _);
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
        //@ open u8s_const(&raw const buffer1[0] as *const u8, 3, _);
        //@ open u8s_const(&raw const buffer1[1] as *const u8, 2, _);
        //@ open u8s_const(&raw const buffer1[2] as *const u8, 1, _);
        //@ open u8s_const(&raw const buffer1[2] as *const u8 as *const u8, 0, _);
    }
}