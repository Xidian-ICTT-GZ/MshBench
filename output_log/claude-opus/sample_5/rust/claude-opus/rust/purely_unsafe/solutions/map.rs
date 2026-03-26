use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Func = unsafe fn(*mut u8, i32) -> i32;

pred nodes(n: *mut Node) =
    n == std::ptr::null_mut()
    ? emp
    : (*n).next |-> ?next &*& (*n).value |-> ?v &*& malloc_block_Node(n) &*& nodes(next);

pred stack(s: *mut Stack) =
    (*s).head |-> ?h &*& malloc_block_Stack(s) &*& nodes(h);

pred i32_at(p: *mut i32) = (*p) |-> ?v;

#[requires(nodes(n) &*& i32_at(data as *mut i32))]
#[ensures(nodes(n) &*& i32_at(data as *mut i32))]
unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8) {
    if n != std::ptr::null_mut() {
        open nodes(n);
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
        close nodes(n);
    }
}

#[requires(nodes(n))]
#[ensures(emp)]
unsafe fn dispose_nodes(n: *mut Node) {
    if n != std::ptr::null_mut() {
        open nodes(n);
        dispose_nodes((*n).next);
        close nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires(true)]
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        close stack(stack);
        return stack;
    }

    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        close nodes(n);
        (*stack).head = n;
        close stack(stack);
    }

    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        open stack(stack);
        let head = (*stack).head;
        open nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        close stack(stack);
        dealloc(head as *mut u8, Layout::new::<Node>());
        return result;
    }

    #[requires(stack(stack) &*& i32_at(data as *mut i32))]
    #[ensures(stack(stack) &*& i32_at(data as *mut i32))]
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8) {
        open stack(stack);
        map_nodes((*stack).head, f, data);
        close stack(stack);
    }

    #[requires(stack(stack))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        open stack(stack);
        dispose_nodes((*stack).head);
        close nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[requires(i32_at(data as *mut i32))]
#[ensures(i32_at(data as *mut i32))]
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

        Stack::map(s, plus_a, &mut a as *mut i32 as *mut u8);

        Stack::dispose(s);
    }
}