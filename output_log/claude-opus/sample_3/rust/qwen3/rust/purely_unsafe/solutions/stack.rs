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
fn node_pred(n: *mut Node, value: i32, next: *mut Node) =
    n |-> Node { next: next, value: value };

#[predicate]
fn stack_list(head: *mut Node) =
    head == std::ptr::null_mut() ?
        emp
    :
        exists<value: i32, next: *mut Node>(node_pred(head, value, next) &*& stack_list(next));

#[predicate]
fn stack_pred(s: *mut Stack, head: *mut Node) =
    s |-> Stack { head: head } &*& stack_list(head);

impl Stack {
    #[requires(Layout::new::<Stack>().size() > 0)]
    #[ensures(result != std::ptr::null_mut() && stack_pred(result, std::ptr::null_mut()))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack != std::ptr::null_mut() && stack_pred(stack, ?old_head))]
    #[ensures(stack_pred(stack, ?new_head) && 
              old_head == new_head || 
              (new_head != std::ptr::null_mut() &&
               exists<value: i32>(node_pred(new_head, value, old_head) && value == value)))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack != std::ptr::null_mut() &&
               stack_pred(stack, ?head) &&
               head != std::ptr::null_mut() &&
               exists<value: i32, next: *mut Node>(node_pred(head, value, next) &*& stack_list(next)))]
    #[ensures(
        result == old_value &&
        stack_pred(stack, old_next)
    )]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack != std::ptr::null_mut() && stack_pred(stack, std::ptr::null_mut()))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}