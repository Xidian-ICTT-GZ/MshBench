use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[verifast::predicate]
pub fn node(n: *mut Node) -> bool {
    n != std::ptr::null_mut()
}

#[verifast::predicate]
pub fn node_list(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        node(n) && node_list(unsafe { (*n).next })
    }
}

#[verifast::predicate]
pub fn stack_inv(s: *mut Stack) -> bool {
    s != std::ptr::null_mut() && node_list(unsafe { (*s).head })
}

#[verifast::requires(node_list(n))]
#[verifast::ensures(true)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[verifast::requires(true)]
    #[verifast::ensures(stack_inv(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        return stack;
    }

    #[verifast::requires(stack_inv(stack))]
    #[verifast::ensures(true)]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        let _head = (*stack).head;

        let result = (*stack).head.is_null();

        return result;
    }

    #[verifast::requires(stack_inv(stack))]
    #[verifast::ensures(stack_inv(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[verifast::requires(stack_inv(stack) && !(*stack).head.is_null())]
    #[verifast::ensures(true)]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        return result;
    }

    #[verifast::requires(stack_inv(stack))]
    #[verifast::ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dispose_nodes((*stack).head);
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