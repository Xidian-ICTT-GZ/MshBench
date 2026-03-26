struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(n: *mut Node, len: i32) =
    match len {
        0 => n.is_null(),
        _ => len > 0 && n != null && 
             exists<next: *mut Node> 
             (*n).next == next && node_list(next, len - 1)
    };

predicate stack(s: *mut Stack, len: i32) =
    s != null && exists<head: *mut Node>
    (*s).head == head && node_list(head, len);

#[requires(stack(stack, ?len))]
#[ensures(stack(stack, len))]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        #[invariant(i >= 0 && node_list(n, ?remaining) && i + remaining == ?len)]
        {
            if n.is_null() {
                break;
            }
            n = (*n).next;
            i += 1;
        }
    }

    i
}