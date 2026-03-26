#![allow(unconditional_recursion)]

predicate valid_buffer(p: *const u8, len: usize) = true;

#[requires(valid_buffer(p1, count))]
#[requires(valid_buffer(p2, count))]
#[ensures(true)]
unsafe fn memcmp(p1: *const u8, p2: *const u8, count: usize) -> i32 {
    let mut result = 0;
    let mut i = 0;
    loop {
        #[invariant(i <= count)]
        {
            if i == count {
                break;
            }
            if *p1.add(i) < *p2.add(i) {
                result = -1;
                break;
            }
            if *p1.add(i) > *p2.add(i) {
                result = 1;
                break;
            }
            i += 1;
        }
    }
    result
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}