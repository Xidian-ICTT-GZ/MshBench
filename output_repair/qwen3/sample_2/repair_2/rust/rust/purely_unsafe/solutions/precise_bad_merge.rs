#[requires(true)]
#[ensures(true)]
fn main() {
    unsafe {
        let mut x: i32 = 0;
        let mut y: i32 = 0;
        core::hint::unreachable_unchecked();
    }
}