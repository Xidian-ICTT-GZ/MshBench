struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(n: *mut Node; count: int) =
    n == null ?
        count == 0
    :
        (*n).next |-> ?next &*& nodes(next, ?rest) &*& count == rest + 1;

predicate stack(s: *mut Stack; count: int) =
    (*s).head |-> ?h &*& nodes(h, count);

#[requires(stack(stack, ?count))]
#[ensures(stack(stack, count) &*& result == count)]
unsafe fn stack_get_count(stack: *mut Stack) -> int {
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(nodes(n, ?remaining) &*& i + remaining == count)]
    while (true) {
        if n == null {
            break;
        }
        n = (*n).next;
        i += 1;
    }

    i
}