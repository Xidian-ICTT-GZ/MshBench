predicate cell(int* p; int v) = p |-> v;

#[requires(cell(p, _))]
#[ensures(cell(p, old(*p)) && result == old(*p))]
fn read_cell(p: int*) -> int {
    unsafe {
        let v = *p;
        v
    }
}

#[requires(cell(p, _))]
#[ensures(cell(p, new_val))]
fn write_cell(p: int*, new_val: int) {
    unsafe {
        *p = new_val;
    }
}

#[requires(true)]
#[ensures(result_cell(cell, v) &*& result == fresh_cell(cell, v))]
fn new_cell(v: int) -> int* {
    let p = unsafe { malloc(sizeof(int)) as int* };
    if p.is_null() {
        std::process::abort();
    }
    unsafe {
        *p = v;
    }
    p
}

#[requires(cell(p, v))]
#[ensures(true)]
fn free_cell(p: int*) {
    unsafe {
        free(p as *mut _);
    }
}