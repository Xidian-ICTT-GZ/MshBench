#![feature(stmt_expr_attributes)]

predicate buf_bytes(p: *const u8, len: usize) = true;

#[requires(buf_bytes(p1, count))]
#[requires(buf_bytes(p2, count))]
#[ensures(result == -1 || result == 0 || result == 1)]
unsafe fn memcmp(p1: *const u8, p2: *const u8, count: usize) -> i32 {
    let mut result = 0;
    let mut i = 0;
    loop {
        #![invariant(i <= count)]
        #![invariant(buf_bytes(p1, count))]
        #![invariant(buf_bytes(p2, count))]
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
    result
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}