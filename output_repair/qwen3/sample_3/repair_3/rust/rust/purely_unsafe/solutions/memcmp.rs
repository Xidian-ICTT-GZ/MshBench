unsafe fn memcmp(p1: *const u8, p2: *const u8, count: usize) -> i32 {
    _verifast_begin!(
        requires(forall(|i: usize| (0 <= i && i < count) ==> (p1.add(i) |-> ?v1) && (p2.add(i) |-> ?v2))));
    _verifast_begin!(ensures(true));
    let mut result = 0;
    let mut i = 0;
    _verifast_loop_invariant!(0 <= i && i <= count);
    _verifast_loop_invariant!(forall(|j: usize| (0 <= j && j < i) ==> *p1.add(j) == *p2.add(j)));
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