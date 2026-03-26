unsafe fn memcmp(p1: *const u8, p2: *const u8, count: usize) -> i32 {
    #[requires(count <= isize::MAX as usize)]
    #[requires(ptr::valid_for(p1, count))]
    #[requires(ptr::valid_for(p2, count))]
    #[ensures(|result| result == -1 || result == 0 || result == 1)]
    let mut result = 0;
    let mut i = 0;
    #[invariant(i <= count)]
    #[invariant(ptr::valid_for(p1, count))]
    #[invariant(ptr::valid_for(p2, count))]
    #[invariant(result == 0)]
    #[invariant(forall(|j: usize| 0 <= j && j < i ==> *p1.add(j) == *p2.add(j)))]
    loop {
        if i == count {
            break;
        }
        let v1 = *p1.add(i);
        let v2 = *p2.add(i);
        if v1 < v2 {
            result = -1;
            break;
        }
        if v1 > v2 {
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