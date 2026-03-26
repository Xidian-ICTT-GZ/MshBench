predicate int_cell(int *p; int v) = p |-> v;

#[requires(true)]
fn main()
{
    unsafe {
        let mut x = 0;
        let mut y = 0;
        // We own the stack variables x and y.
        // To be explicit about ownership, specify that &x and &y point to initial values.
        // VeriFast models stack variables as heap locations.
        // So we open ownership of int_cell(&x, 0) and int_cell(&y, 0).

        // Claim ownership of both integers on stack
        open int_cell(&x, 0);
        open int_cell(&y, 0);

        // We own &x and &y with initial value 0 each.

        std::hint::unreachable_unchecked();

        // unreachable_unchecked terminates, so no ensures needed.
    }
}