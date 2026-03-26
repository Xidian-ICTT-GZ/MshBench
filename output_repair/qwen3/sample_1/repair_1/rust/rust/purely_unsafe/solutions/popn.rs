use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[verifast::predicate]
pub fn node_list(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        std::ptr::read(n); // dummy read to satisfy ownership
        node_list(unsafe { (*n).next })
    }
}

#[verifast::predicate]
pub fn stack_inv(s: *mut Stack) -> bool {
    std::ptr::read(s);
    node_list(unsafe { (*s).head })
}

#[verifast::requires(true)]
#[verifast::ensures(stack_inv(result))]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
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

        stack
    }

    #[verifast::requires(stack_inv(stack))]
    #[verifast::ensures(stack_inv(stack))]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        let head = (*stack).head;

        let result = (*stack).head.is_null();

        result
    }

    #[verifast::requires(stack_inv(stack))]
    #[verifast::ensures(stack_inv(stack))]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
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
    #[verifast::ensures(stack_inv(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[verifast::requires(stack_inv(stack) && n >= 0)]
    #[verifast::ensures(stack_inv(stack))]
    #[verifast::invariant(i >= 0 && i <= n && stack_inv(stack))]
    unsafe fn popn(stack: *mut Stack, n: i32) {
        let mut i = 0;
        loop {
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }

    #[verifast::requires(stack_inv(stack))]
    #[verifast::ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        let mut n = (*stack).head;
        loop {
            if n.is_null() {
                break;
            }

            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }

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