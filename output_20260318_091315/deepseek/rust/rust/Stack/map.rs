use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Func = unsafe fn(*mut u8, i32) -> i32;

#[predicate]
fn node(n: *mut Node, value: i32, next: *mut Node) -> bool {
    struct Node { next: *mut Node, value: i32 } &&
    n != std::ptr::null_mut() &&
    (*n).value == value && (*n).next == next
}

#[predicate]
fn nodes(n: *mut Node) -> bool {
    n == std::ptr::null_mut() ? true :
        exists![value: i32, next: *mut Node ->
            node(n, value, next) && nodes(next)]
}

#[predicate]
fn stack(s: *mut Stack) -> bool {
    struct Stack { head: *mut Node } &&
    s != std::ptr::null_mut() &&
    exists![head: *mut Node -> (*s).head == head && nodes(head)]
}

#[predicate]
fn i32_ptr(p: *mut i32) -> bool {
    p != std::ptr::null_mut()
}

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
    #[requires(nodes(n))]
    #[requires(i32_ptr(data as *mut i32))]
    #[ensures(nodes(n))]
{
    if !n.is_null() {
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    #[requires(nodes(n))]
    #[ensures(true)]
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        #[ensures(stack(result))]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        return stack;
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
        #[requires(stack(stack))]
        #[ensures(stack(stack))]
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        #[requires(stack(stack))]
        #[requires((*stack).head != std::ptr::null_mut())]
        #[ensures(stack(stack))]
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        return result;
    }
    
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
        #[requires(stack(stack))]
        #[requires(i32_ptr(data as *mut i32))]
        #[ensures(stack(stack))]
    {
        map_nodes((*stack).head, f, data);
    }
    
    unsafe fn dispose(stack: *mut Stack)
        #[requires(stack(stack))]
        #[ensures(true)]
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn plus_a(data: *mut u8, x: i32) -> i32
    #[requires(i32_ptr(data as *mut i32))]
    #[ensures(result == x + *(data as *mut i32))]
{
    let result = x + *(data as *mut i32);
    result
}

unsafe fn read_i32() -> i32
    #[ensures(true)]
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.parse().unwrap()
}

fn main()
    #[ensures(true)]
{
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