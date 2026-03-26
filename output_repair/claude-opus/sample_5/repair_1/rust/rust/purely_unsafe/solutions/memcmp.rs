#[predicate]
fn bytes_readable(p: *const u8, len: usize) = true;

#[requires(bytes_readable(p1, count))]
#[requires(bytes_readable(p2, count))]
#[ensures(result == -1 || result == 0 || result == 1)]
unsafe fn memcmp(p1: *const u8, p2: *const u8, count: usize) -> i32 {
    let mut result = 0;
    let mut i = 0;
    #[invariant(i <= count)]
    #[invariant(bytes_readable(p1, count))]
    #[invariant(bytes_readable(p2, count))]
    loop {
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