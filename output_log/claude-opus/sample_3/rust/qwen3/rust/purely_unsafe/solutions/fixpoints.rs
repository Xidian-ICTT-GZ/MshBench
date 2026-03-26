use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_pred(n: *mut Node) = n != std::ptr::null_mut() &*&
    n |-> Node { next: ?next_node, value: ?v } &*&
    true;

#[predicate]
fn linked_list(n: *mut Node) = 
    n == std::ptr::null_mut() ?
        emp
    :
        node_pred(n) * linked_list(unsafe { (*n).next });

#[predicate]
fn stack_pred(s: *mut Stack, head: *mut Node) = s != std::ptr::null_mut() &*&
    s |-> Stack { head: head } * linked_list(head);

#[requires(Layout::new::<Stack>().size() > 0 && Layout::new::<Stack>().align() > 0)]
#[ensures(result != std::ptr::null_mut())]
#[ensures(stack_pred(result, std::ptr::null_mut()))]
unsafe fn stack_create() -> *mut Stack {
    let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
    if stack.is_null() {
        handle_alloc_error(Layout::new::<Stack>());
    }
    (*stack).head = std::ptr::null_mut();

    stack
}

#[requires(stack_pred(stack, ?old_head))]
#[ensures(stack_pred(stack, ?new_head))]
unsafe fn stack_push(stack: *mut Stack, value: i32)
    requires stack_pred(stack, ?old_head),
    ensures stack_pred(stack, ?new_head),
    ensures new_head != std::ptr::null_mut(),
    ensures {
        old_head == (*new_head).next
    }
{
    let n = alloc(Layout::new::<Node>()) as *mut Node;
    if n.is_null() {
        handle_alloc_error(Layout::new::<Node>());
    }
    (*n).next = (*stack).head;
    (*n).value = value;
    (*stack).head = n;
}

#[requires(stack_pred(stack, ?head) &*& head != std::ptr::null_mut() &*& node_pred(head))]
#[ensures(stack_pred(stack, ?next))]
#[ensures(result == unsafe { (*head).value })]
unsafe fn stack_pop(stack: *mut Stack) -> i32 {
    let head = (*stack).head;

    let result = (*head).value;
    (*stack).head = (*head).next;
    dealloc(head as *mut u8, Layout::new::<Node>());

    result
}

#[requires(stack_pred(stack, ?head))]
#[ensures(emp)]
unsafe fn stack_dispose(stack: *mut Stack)
    requires stack_pred(stack, ?head),
    ensures emp
{
    let mut current = (*stack).head;
    while (current != std::ptr::null_mut())
        invariant linked_list(current)
    {
        let next = (*current).next;
        dealloc(current as *mut u8, Layout::new::<Node>());
        current = next;
    }
    dealloc(stack as *mut u8, Layout::new::<Stack>());
}

fn main() {
    unsafe {
        let s = stack_create();
        stack_push(s, 10);
        stack_push(s, 20);
        let result1 = stack_pop(s);

        let result2 = stack_pop(s);

        stack_dispose(s);
    }
}