pred u8_array(p: *const u8, count: usize) =
    if count == 0 {
        true
    } else {
        *p |-> ?v &*& u8_array(p.add(1), count - 1)
    };

pred u8_array_slice(p: *const u8, start: usize, count: usize) =
    if start >= count {
        true
    } else {
        *p.add(start) |-> ?v &*& u8_array_slice(p, start + 1, count)
    };

#[requires(u8_array(p1, count) &*& u8_array(p2, count))]
#[ensures(u8_array(p1, count) &*& u8_array(p2, count) &*&
          (result == -1 || result == 0 || result == 1))]
unsafe fn memcmp(p1: *const u8, p2: *const u8, count: usize) -> i32 {
    let mut result = 0;
    let mut i = 0;
    #[invariant(
        i <= count &*&
        u8_array(p1, count) &*&
        u8_array(p2, count) &*&
        (result == -1 || result == 0 || result == 1) &*&
        // prefix elements [0..i) of p1 and p2 are equal
        (forall(|k: int| 0 <= k && k < i ==> *p1.add(k) == *p2.add(k)))
    )]
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