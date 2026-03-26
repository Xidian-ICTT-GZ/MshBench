unsafe fn memcmp(p1: *const u8, p2: *const u8, count: usize) -> i32
//@ requires u8_array(p1, count, ?cs1) &*& u8_array(p2, count, ?cs2);
//@ ensures u8_array(p1, count, cs1) &*& u8_array(p2, count, cs2) &*& (result == -1 || result == 0 || result == 1);
{
    let mut result = 0;
    let mut i = 0;
    loop {
        //@ invariant 0 <= i &*& i <= count &*& u8_array(p1, count, cs1) &*& u8_array(p2, count, cs2) &*& (result == -1 || result == 0 || result == 1);
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