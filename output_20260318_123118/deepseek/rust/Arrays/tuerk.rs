use std::io::{Read, Write, stdin, stdout};

/*@
predicate_ctor stdin_state(any info) = true;
predicate_ctor stdout_state(any info) = true;

predicate stdin_io() = 
    [_]stdin_state(()) &*&
    [_]exists<|?stdin_handle|> @stdin_handle |> stdin_state(());

predicate stdout_io() = 
    [_]stdout_state(()) &*&
    [_]exists<|?stdout_handle|> @stdout_handle |> stdout_state(());
@*/

#[requires(stdin_io())]
#[ensures(stdin_io())]
unsafe fn read_byte() -> u8
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(stdout_io())]
#[ensures(stdout_io())]
unsafe fn write_byte(value: u8)
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

/*@
predicate u8_slice(*mut u8 start, usize count; list<u8> contents) =
    count == 0 ?
        start == core::ptr::null_mut()
    :
        integer(start, ?val) &*&
        u8_slice(start.offset(1), count - 1, ?tail) &*&
        contents == cons(val, tail);

predicate_ctor alloc_layout(usize count, any info) = true;

lemma void split_u8_slice(*mut u8 start, usize i, usize count);
    requires u8_slice(start, count, ?contents) &*& 0 <= i &*& i <= count;
    ensures u8_slice(start, i, take(i, contents)) &*& u8_slice(start.offset(i), count - i, drop(i, contents));

lemma void merge_u8_slice(*mut u8 start, usize i, usize count);
    requires u8_slice(start, i, ?prefix) &*& u8_slice(start.offset(i), count - i, ?suffix);
    ensures u8_slice(start, count, append(prefix, suffix));
@*/

#[requires(count <= usize::MAX)]
#[ensures(result.is_null() ? count == 0 : u8_slice(result, count, _))]
unsafe fn alloc(count: usize) -> *mut u8
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(stdin_io())]
#[requires(!start.is_null())]
#[requires(u8_slice(start, count, _))]
#[ensures(stdin_io())]
#[ensures(u8_slice(start, count, _))]
unsafe fn read_bytes(start: *mut u8, count: usize)
{
    let mut i = 0;
    loop {
        #[invariant(stdin_io())]
        #[invariant(i <= count)]
        #[invariant(u8_slice(start, i, ?prefix))]
        #[invariant(u8_slice(start.offset(i), count - i, _))]
        
        if i == count {
            break;
        }
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
    }
}

#[requires(stdout_io())]
#[requires(!start.is_null())]
#[requires(u8_slice(start, count, ?contents))]
#[ensures(stdout_io())]
#[ensures(u8_slice(start, count, contents))]
unsafe fn write_bytes(start: *mut u8, count: usize)
{
    let mut i = 0;
    loop {
        #[invariant(stdout_io())]
        #[invariant(i <= count)]
        #[invariant(u8_slice(start, i, take(i, ?contents)))]
        #[invariant(u8_slice(start.offset(i), count - i, drop(i, contents)))]
        
        if i == count { break; }
        
        write_byte(*start.add(i));
        i += 1;
    }
}

fn main() {
    unsafe {
        #[requires(true)]
        #[ensures(stdin_io())]
        #[ensures(stdout_io())]
        {
            let array = alloc(100);
            read_bytes(array, 100);
            write_bytes(array, 100);
            write_bytes(array, 100);
        }
    }
}