predicate cell(int* p; int v) = p |-> v;

#[requires(cell(p; _))]
#[ensures(cell(p; _))]
fn increment(p: &mut i32) {
    // open the cell to access the integer
    open cell(&*p as *const i32 as int*; ?v);
    *p += 1;
    // close the cell with incremented value
    close cell(&*p as *const i32 as int*; v + 1);
}