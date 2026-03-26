use std::io::{stdin, stdout, Read, Write};

predicate u8s(ptr: *mut u8, count: usize; vs: std::vec::Vec<u8>) =
    if count == 0 {
        vs.len() == 0
    } else {
        vs.len() == count &*&
        *ptr |-> vs[0] &*&
        u8s(ptr.wrapping_add(1), count - 1, vs[1..].to_vec())
    };

predicate u8s_uninit(ptr: *mut u8, count: usize) =
    if count == 0 {
        false == false // failsafe to avoid trivial predicate, see below
    } else {
        *ptr |-> _ &*&
        u8s_uninit(ptr.wrapping_add(1), count - 1)
    };

// To avoid forbidden trivial predicates: 
// u8s_uninit(0,0) is false == false == true but must mention heap.
// We improve it by disallowing zero counts for u8s_uninit:
lemma void u8s_uninit_nonzero_count()
    requires true;
    ensures forall (ptr: *mut u8, count: usize) -> bool {
        count == 0 ==> false; // no ownership for zero count
    }
{}

#[ensures(result != std::ptr::null_mut())]
unsafe fn read_byte() -> u8
    //@ requires true;
    //@ ensures true;
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(true)]
#[ensures(true)]
unsafe fn write_byte(value: u8)
    //@ requires true;
    //@ ensures true;
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(count > 0)]
#[ensures(u8s_uninit(result, count))]
unsafe fn alloc(count: usize) -> *mut u8
    //@ requires count > 0;
    //@ ensures u8s_uninit(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    assume(u8s_uninit(result, count));
    result
}

#[requires(u8s_uninit(start, count) &*& count > 0)]
#[ensures(u8s(start, count, ?vs) &*& vs.len() == count)]
unsafe fn read_bytes(start: *mut u8, count: usize)
    //@ requires u8s_uninit(start, count) &*& count > 0;
    //@ ensures u8s(start, count, ?vs) &*& vs.len() == count;
{
    let mut i = 0;
    #[invariant(i <= count &*& exists (vs1: std::vec::Vec<u8>, vs2: std::vec::Vec<u8>) &*&
         vs1.len() == i &*& vs2.len() == count - i &*&
         u8s(start, i, vs1) &*& u8s_uninit(start.wrapping_add(i), count - i))]
    loop {
        if i == count {
            break;
        }
        let b = read_byte();

        *start.add(i) = b;

        i += 1;
    }
}

#[requires(u8s(start, count, ?vs))]
#[ensures(u8s(start, count, vs))]
unsafe fn write_bytes(start: *mut u8, count: usize)
    //@ requires u8s(start, count, ?vs);
    //@ ensures u8s(start, count, vs);
{
    let mut i = 0;
    #[invariant(i <= count &*& u8s(start, count, vs))]
    loop {
        if i == count {
            break;
        }

        let b = *start.add(i);

        write_byte(b);
        i += 1;
    }
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}