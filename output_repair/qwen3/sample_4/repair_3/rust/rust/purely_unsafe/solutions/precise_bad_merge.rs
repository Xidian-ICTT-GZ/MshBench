#[requires(true)]
#[ensures(true)]
fn main() {
    unsafe {
        let mut x = 0;
        let mut y = 0;

        core::hint::unreachable_unchecked();
    }
}