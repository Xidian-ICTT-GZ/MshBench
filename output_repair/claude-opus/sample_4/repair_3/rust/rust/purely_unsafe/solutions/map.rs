use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Func = unsafe fn(*mut u8, i32) -> i32;

#[requires(n.is_null() || Owned(n) && Owned((*n).next))]
#[ensures(emp)]
unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8) {
    if !n.is_null() {
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
    }
}

#[requires(n.is_null() || Owned(n) && Owned((*n).next))]
#[ensures(emp)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[ensures(Owned(result) && Owned((*result).head))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        return stack;
    }

    #[requires(Owned(stack) && Owned((*stack).head))]
    #[ensures(Owned(stack) && Owned((*stack).head))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(Owned(stack) && Owned((*stack).head))]
    #[ensures(Owned(stack) && Owned((*stack).head))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        return result;
    }

    #[requires(Owned(stack) && Owned((*stack).head))]
    #[ensures(Owned(stack) && Owned((*stack).head))]
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8) {
        map_nodes((*stack).head, f, data);
    }

    #[requires(Owned(stack) && Owned((*stack).head))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[requires(true)]
#[ensures(emp)]
unsafe fn plus_a(data: *mut u8, x: i32) -> i32 {
    let result = x + *(data as *mut i32);

    result
}

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