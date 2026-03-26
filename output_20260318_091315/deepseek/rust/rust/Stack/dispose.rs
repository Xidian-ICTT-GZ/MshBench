use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn nodes(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        let node = unsafe { &*n };
        nodes(node.next)
    }
}

#[predicate]
fn stack(stack: *mut Stack) -> bool {
    if stack.is_null() {
        false
    } else {
        let s = unsafe { &*stack };
        nodes(s.head)
    }
}

#[predicate]
fn node_own(n: *mut Node) -> bool {
    !n.is_null()
}

#[predicate]
fn stack_own(stack: *mut Stack) -> bool {
    !stack.is_null()
}

unsafe fn dispose_nodes(n: *mut Node)
    #[requires(nodes(n))]
    #[ensures(true)]
{
    if !n.is_null() {
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        #[ensures(stack_own(result) && stack(result))]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        return stack;
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
        #[requires(stack_own(stack) && stack(stack))]
        #[ensures(stack_own(stack) && stack(stack))]
    {
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        return result;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        #[requires(stack_own(stack) && stack(stack))]
        #[ensures(stack_own(stack) && stack(stack))]
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
        #[requires(stack_own(stack) && stack(stack) && !(*stack).head.is_null())]
        #[ensures(stack_own(stack) && stack(stack))]
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        return result;
    }
    
    unsafe fn dispose(stack: *mut Stack)
        #[requires(stack_own(stack) && stack(stack))]
        #[ensures(true)]
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}