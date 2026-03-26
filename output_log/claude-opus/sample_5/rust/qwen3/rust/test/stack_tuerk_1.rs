#[pred]
struct StackNode {
    next: *mut StackNode,
}

#[pred]
struct Stack {
    head: *mut StackNode,
}

#[pred]
fn stack_node_list(p: *mut StackNode, len: i32) =
    (p == 0 && len == 0) ||
    (p != 0 && pts_to(p, StackNode { next: ?q }) &*& stack_node_list(q, ?m) &*& len == m + 1);

unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    #[requires(
        stack != 0 && 
        pts_to(stack, Stack { head: ?head }) &*&
        stack_node_list(head, ?len)
    )]
    #[ensures(
        pts_to(stack, Stack { head: ?head2 }) &*&
        stack_node_list(head2, len) &*&
        result == len
    )]
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        #[invariant(
            pts_to(stack, Stack { head: head }) &*&
            stack_node_list(n, ?remaining) &*&
            i + remaining == len &*&
            (n == 0 || pts_to(n, StackNode { next: ?next }))
        )]
        if n.is_null() {
            break;
        }
        let next = (*n).next;
        n = next;
        i += 1;
    }

    i
}

#[pred]
fn stack_list(p: *mut StackNode, len: usize) =
    (p == 0 && len == 0) ||
    (p != 0 && pts_to(p, StackNode { next: ?q }) &*& stack_node_list(q, ?m) &*& len == m + 1);