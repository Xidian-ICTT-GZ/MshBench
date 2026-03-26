use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

#[predicate]
fn node(n: *mut Node, value: i32, next: *mut Node) -> bool {
    struct Node { next: *mut Node, value: i32 } &&
    n != std::ptr::null_mut() &&
    (*n).value == value &&
    (*n).next == next
}

#[predicate]
fn nodes(n: *mut Node) -> bool {
    n == std::ptr::null_mut() ? true :
        exists![value: i32, next: *mut Node ->
            node(n, value, next) * nodes(next)
        ]
}

#[predicate]
fn stack(s: *mut Stack) -> bool {
    struct Stack { head: *mut Node } &&
    s != std::ptr::null_mut() &&
    exists![head: *mut Node -> (*s).head == head && nodes(head)]
}

#[requires(stack(s))]
#[ensures(stack(s))]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
{
    if !(*n).is_null() {
        #[invariant(stack(s))]
        #[invariant(exists![head: *mut Node -> *n == head && nodes(head)])]
        {
            let keep = p((**n).value);
            if keep {
                filter_nodes(&raw mut (**n).next, p);
            } else {
                let next_ = (**n).next;
                dealloc(*n as *mut u8, Layout::new::<Node>());
                *n = next_;
                filter_nodes(n, p);
            }
        }
    }
}

#[requires(nodes(n))]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node)
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[ensures(result != std::ptr::null_mut() && stack(result))]
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    #[requires(stack(s))]
    #[ensures(stack(s))]
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(s) && (*s).head != std::ptr::null_mut())]
    #[ensures(stack(s))]
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }
    
    #[requires(stack(s))]
    #[ensures(stack(s))]
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    {
        filter_nodes(&raw mut (*stack).head, p);
    }
    
    #[requires(stack(s))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[ensures(result == (x != 20))]
unsafe fn neq_20(x: i32) -> bool
{
    x != 20
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}