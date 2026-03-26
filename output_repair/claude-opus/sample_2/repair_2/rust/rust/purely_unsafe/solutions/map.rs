use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Func = unsafe fn(*mut u8, i32) -> i32;

predicate node_list(n: *mut Node) =
    n.is_null() ? emp : (
        n as usize != 0 &&
        Owned(n) &&
        Owned((*n).next) &&
        node_list((*n).next)
    );

predicate stack_inv(s: *mut Stack) =
    s as usize != 0 &&
    Owned(s) &&
    node_list((*s).head);

#[requires(n as usize == 0 || node_list(n))]
#[ensures(n as usize == 0 || node_list(n))]
unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8) {
    if !n.is_null() {
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
    }
}

#[requires(n as usize == 0 || node_list(n))]
#[ensures(emp)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[ensures(stack_inv(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        return stack;
    }

    #[requires(stack_inv(stack))]
    #[ensures(stack_inv(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_inv(stack))]
    #[ensures(stack_inv(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        return result;
    }

    #[requires(stack_inv(stack))]
    #[ensures(stack_inv(stack))]
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8) {
        map_nodes((*stack).head, f, data);
    }

    #[requires(stack_inv(stack))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[requires(data as usize != 0)]
#[ensures(true)]
unsafe fn plus_a(data: *mut u8, x: i32) -> i32 {
    let result = x + *(data as *mut i32);

    result
}

#[ensures(true)]
unsafe fn read_i32() -> i32 {
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.parse().unwrap()
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::push(s, 30);
        let mut a = read_i32();

        Stack::map(s, plus_a, &raw mut a as *mut u8);

        Stack::dispose(s);
    }
}