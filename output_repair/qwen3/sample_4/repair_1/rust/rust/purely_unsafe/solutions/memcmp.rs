unsafe fn memcmp(p1: *const u8, p2: *const u8, count: usize) -> i32 {
    #[requires(forall(i: usize, 0 <= i && i < count) ==>
               sep(
                   (p1 + i) |-> ?v1,
                   (p2 + i) |-> ?v2
               ))]
    #[ensures(true)]
    let mut result = 0;
    let mut i = 0;
    #[invariant(i <= count)]
    #[invariant(forall(j: usize, 0 <= j && j < i) ==>
                sep(
                    (p1 + j) |-> ?v1,
                    (p2 + j) |-> ?v2
                ))]
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