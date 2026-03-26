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
    if n.is_null() {
        emp
    } else {
        (*n).next |-> ?next &*& (*n).value |-> ?v &*& malloc_block_Node(n) &*& nodes(next)
    };

pred stack(s: *mut Stack) = 
    (*s).head |-> ?h &*& malloc_block_Stack(s) &*& nodes(h);

pred i32_at(p: *mut i32) = p |-> _ &*& malloc_block(p, sizeof(int));

#[requires(nodes(n) &*& i32_at(data as *mut i32))]
#[ensures(nodes(n) &*& i32_at(data as *mut i32))]
unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8) {
    if !n.is_null() {
        (*n).next |-> ?next &*& (*n).value |-> ?v &*& malloc_block_Node(n) &*& nodes(next) &*& i32_at(data as *mut i32);
        let y = f(data, v);
        (*n).value = y;
        map_nodes(next, f, data);
    }
}

#[requires(nodes(n))]
#[ensures(emp)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        (*n).next |-> ?next &*& (*n).value |-> _ &*& malloc_block_Node(n) &*& nodes(next);
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires(emp)]
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        (*stack).head |-> ?old_head &*& malloc_block_Stack(stack) &*& nodes(old_head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = old_head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack) &*& !((*stack).head).is_null())]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        (*stack).head |-> ?head &*& malloc_block_Stack(stack) &*& nodes(head);
        head |-> n_next &*& (*head).value |-> ?v &*& malloc_block_Node(head) &*& nodes(n_next);

        let result = v;
        (*stack).head = n_next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack(stack) &*& i32_at(data as *mut i32))]
    #[ensures(stack(stack) &*& i32_at(data as *mut i32))]
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8) {
        (*stack).head |-> ?h &*& malloc_block_Stack(stack) &*& nodes(h) &*& i32_at(data as *mut i32);
        map_nodes(h, f, data);
    }

    #[requires(stack(stack))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        (*stack).head |-> ?h &*& malloc_block_Stack(stack) &*& nodes(h);
        dispose_nodes(h);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[requires(i32_at(data as *mut i32))]
#[ensures(i32_at(data as *mut i32))]
unsafe fn plus_a(data: *mut u8, x: i32) -> i32 {
    *(data as *mut i32) |-> ?a &*& malloc_block(data as *mut u8, sizeof(int));
    let result = x + a;
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