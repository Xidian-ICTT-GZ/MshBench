predicate int_cell(int *p; int v) = p |-> v;

#[requires(true)]
#[ensures(true)]
fn main() {
    unsafe {
        let mut x = 0;
        let mut y = 0;
        int_cell(&mut x, 0) &*& int_cell(&mut y, 0);

        std::hint::unreachable_unchecked();
    }
}