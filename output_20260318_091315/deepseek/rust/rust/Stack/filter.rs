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
fn nodes(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        let node = unsafe { &*n };
        nodes(node.next)
    }
}

#[predicate]
fn nodes_with_value(n: *mut Node, v: i32) -> bool {
    if n.is_null() {
        true
    } else {
        let node = unsafe { &*n };
        node.value == v && nodes_with_value(node.next, v)
    }
}

#[predicate]
fn stack(stk: *mut Stack) -> bool {
    if stk.is_null() {
        false
    } else {
        let stack = unsafe { &*stk };
        nodes(stack.head)
    }
}

#[predicate]
fn stack_with_head(stk: *mut Stack, h: *mut Node) -> bool {
    if stk.is_null() {
        false
    } else {
        let stack = unsafe { &*stk };
        stack.head == h && nodes(h)
    }
}

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
#[requires(nodes(n))]
#[ensures(nodes(result))]
{
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);
            (*n).next = next;
            n
        } else {
            next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            result
        }
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
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    #[requires(stack(stack))]
    #[ensures(stack_with_head(stack, old((*stack).head)))]
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
    #[requires(!(*stack).head.is_null() && stack(stack))]
    #[ensures(stack_with_head(stack, old((*stack).head)))]
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    #[requires(stack(stack))]
    #[ensures(stack_with_head(stack, old((*stack).head)))]
    {
        let head = filter_nodes((*stack).head, p);
        (*stack).head = head;
    }
    
    unsafe fn dispose(stack: *mut Stack)
    #[requires(stack(stack))]
    #[ensures(true)]
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool
#[ensures(result == (x != 20))]
{
    x != 20
}

fn main()
#[ensures(true)]
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}