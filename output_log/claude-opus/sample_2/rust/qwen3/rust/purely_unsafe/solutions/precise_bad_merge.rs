predicate is_vec<T>(v: &Vec<T>, list: list<T>) =
    v@.len == length(list) &*&
    v@.content == list &*&
    v->Vec{content: list};

#[requires(is_vec(v, ?list))]
#[ensures(is_vec(v, list))]
fn no_op<T>(v: &Vec<T>) {
    // This function does nothing, consuming and restoring full ownership of v
}