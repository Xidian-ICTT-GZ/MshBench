struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(n: *mut Node; count: i32) =
    if n.is_null() {
        count == 0
    } else {
        (*n).next |-> ?next &*& nodes(next, ?rest) &*& count == rest + 1
    };

predicate stack(s: *mut Stack; count: i32) =
    (*s).head |-> ?h &*& nodes(h, count);

#[requires(stack(stack, ?count))]
#[ensures(stack(stack, count) &*& result == count)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(nodes(n, ?remaining) &*& i + remaining == count)]
    loop {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }

    i
}