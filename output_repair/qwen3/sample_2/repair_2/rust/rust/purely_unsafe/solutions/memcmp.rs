#![feature(stmt_expr_attributes)]

unsafe fn memcmp(p1: *const u8, p2: *const u8, count: usize) -> i32 {
    #[requires(forall(i: usize, i < count ==> (p1.add(i)) |-> ?v1 &*& (p2.add(i)) |-> ?v2))]
    #[ensures(true)]
    {
        let mut result = 0;
        let mut i = 0;
        #[invariant(i <= count &*&
                    forall(j: usize, j < i ==> (p1.add(j)) |-> ?v1j &*& (p2.add(j)) |-> ?v2j &*& v1j == v2j))]
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
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}