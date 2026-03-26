#[derive(Clone, Copy)]
struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(n: *mut Node; count: i32) =
    match n == std::ptr::null_mut() {
        true => count == 0,
        false => exists_next(next: *mut Node, rest_count: i32)
            (*n).next |-> next &*& nodes(next, rest_count) &*& count == 1 + rest_count
    };

predicate stack(s: *mut Stack; count: i32) =
    s != std::ptr::null_mut() &*&
    (*s).head |-> head &*& nodes(head, count);

unsafe fn stack_get_count(stack: *mut Stack) -> i32
    requires stack(stack, ?count),
    ensures stack(stack, count) &*& result == count;
{
    let mut n = (*stack).head;
    let mut i = 0;
    loop
        invariant
            stack != std::ptr::null_mut() &*&
            (*stack).head |-> n &*&
            nodes(n, ?remaining) &*&
            i + remaining == count;
    {
        if n.is_null() {
            break;
        }
        let next = (*n).next;
        n = next;
        i += 1;
    }

    i
}