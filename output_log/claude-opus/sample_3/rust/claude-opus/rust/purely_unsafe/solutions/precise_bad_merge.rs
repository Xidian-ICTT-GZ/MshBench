predicate cell(int *p; int v) = p |-> v;

fn main()
    #[requires(true)]
    #[ensures(true)]
{
    unsafe {
        let mut x = 0;
        let mut y = 0;
        // At this point, we own `x` and `y` as two distinct cells on the stack
        // We state that using cell predicates for each.
        // Introduce predicates for the local variables:
        // Note: The stack variables are modeled as pointers to ints in VeriFast,
        // here we treat &mut x and &mut y as int* pointers.
        // We can assert ownership of their cells before unreachable call.

        // However, since the code uses no explicit pointers,
        // we use fixpoint to get addresses and assert ownership.

        // Extract pointers:
        let px: *mut int = &mut x;
        let py: *mut int = &mut y;

        // We now have two cells for px and py initialized to 0.
        // We can package this ownership for verification:
        //
        // Unfortunately, VeriFast does not verify local stack variables ownership implicitly,
        // so we add manual proof that we own these cells.

        #[predicate]
        fn local_cells(int *px, int *py) = 
            cell(px; 0) * cell(py; 0);

        // Pack ownership:
        open local_cells(px, py);
        close local_cells(px, py);

        // Now call to unreachable_unchecked requires that the code is unreachable,
        // so the function postcondition is unreachable.

        std::hint::unreachable_unchecked();
    }
}