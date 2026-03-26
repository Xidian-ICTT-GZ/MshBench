pred u8_array(p: *const u8, count: usize) =
    count > 0 ? *p |-> ?v &*& u8_array(p.add(1), count - 1) : emp;

pred u8_array_slice(p: *const u8, start: usize, count: usize) =
    start < count ? *p.add(start) |-> ?v &*& u8_array_slice(p, start + 1, count) : emp;

#[requires(u8_array(p1, count) &*& u8_array(p2, count))]
#[ensures(u8_array(p1, count) &*& u8_array(p2, count))]
unsafe fn memcmp(p1: *const u8, p2: *const u8, count: usize) -> i32 {
    let mut result = 0;
    let mut i = 0;
    #[invariant(
        0 <= i &*& i <= count &*&
        u8_array(p1, count) &*&
        u8_array(p2, count) &*&
        (result == -1 || result == 0 || result == 1)
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