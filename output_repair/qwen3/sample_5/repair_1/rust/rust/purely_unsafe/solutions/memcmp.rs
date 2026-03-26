unsafe fn memcmp(p1: *const u8, p2: *const u8, count: usize) -> i32 {
    #[requires(forall(i: usize; 0 <= i && i < count ==> (p1 + i) |-> ?v1_i &*& (p2 + i) |-> ?v2_i))]
    #[ensures(forall(i: usize; 0 <= i && i < count ==> (p1 + i) |-> _ &*& (p2 + i) |-> _))]
    let mut result = 0;
    let mut i = 0;
    #[invariant(0 <= i && i <= count)]
    #[invariant(forall(j: usize; 0 <= j && j < i ==> (p1 + j) |-> ?v1_j &*& (p2 + j) |-> ?v2_j &*& v1_j == v2_j))]
    #[invariant(forall(j: usize; i <= j && j < count ==> (p1 + j) |-> _ &*& (p2 + j) |-> _))]
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