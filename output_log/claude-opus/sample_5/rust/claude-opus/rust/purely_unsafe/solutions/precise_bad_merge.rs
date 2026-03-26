#[predicate]
fn cell(x: *mut i32, v: int) = x |-> v

#[requires(true)]
#[ensures(true)]
fn main() {
    unsafe {
        let mut x = 0;
        let mut y = 0;

        std::hint::unreachable_unchecked();
    }
}