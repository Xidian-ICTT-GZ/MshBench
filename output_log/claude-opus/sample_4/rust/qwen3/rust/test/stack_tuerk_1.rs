#[pred]
struct StackNode {
    next: *mut StackNode,
}

#[pred]
struct Stack {
    head: *mut StackNode,
}

#[predicate]
fn stack_node_list(p: *mut StackNode, len: int) =
    p == 0 ? len == 0 : pts_to(p, StackNode { next: ?q }) &*& stack_node_list(q, ?m) &*& len == m + 1;

unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    #[requires(
        stack != 0 && 
        pts_to(stack, Stack { head: ?head }) &*&
        stack_node_list(head, ?len)
    )]
    #[ensures(
        pts_to(stack, Stack { head: ?head }) &*&
        stack_node_list(head, len) &*&
        result == len
    )]
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        #[invariant(
            pts_to(stack, Stack { head: head }) &*&
            stack_node_list(head, len) &*&
            (n == 0 ? i == len : 
                pts_to(n, StackNode { next: ?next }) &*&
                stack_node_list(n, ?remaining) &*&
                i + remaining == len
            )
        )]
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }

    i
}

#[pred]
fn stack_node_list(p: *mut StackNode, len: int) =
    p == 0 ? len == 0 : pts_to(p, StackNode { next: ?q }) &*& stack_node_list(q, ?m) &*& len == m + 1;