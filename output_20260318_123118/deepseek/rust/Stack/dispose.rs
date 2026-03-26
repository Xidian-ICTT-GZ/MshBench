use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_own(n: *mut Node, v: i32, next: *mut Node) -> bool {
    addr_of!((*n).value) != 0 && addr_of!((*n).next) != 0 &&
    struct_ty!(*n, Node) &&
    (*n).value == v && (*n).next == next
}

#[predicate]
fn nodes(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        exists!(let v: i32; exists!(let next: *mut Node;
            node_own(n, v, next) &*& nodes(next)))
    }
}

#[predicate]
fn stack_own(s: *mut Stack, head: *mut Node) -> bool {
    addr_of!((*s).head) != 0 &&
    struct_ty!(*s, Stack) &&
    (*s).head == head
}

#[predicate]
fn stack(s: *mut Stack) -> bool {
    exists!(let head: *mut Node;
        stack_own(s, head) &*& nodes(head))
}

unsafe fn dispose_nodes(n: *mut Node)
    requires nodes(n);
    ensures true;
{
    if !n.is_null() {
        let next = (*n).next;
        let v = (*n).value;
        open nodes(n);
        open node_own(n, v, next);
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[ensures(result != 0 && stack(result))]
    unsafe fn create() -> *mut Stack
    {
        let layout = Layout::new::<Stack>();
        let stack = alloc(layout) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(layout);
        }
        (*stack).head = std::ptr::null_mut();
        close nodes(std::ptr::null_mut());
        close stack_own(stack, std::ptr::null_mut());
        close stack(stack);
        return stack;
    }
    
    #[requires(stack(s))]
    #[ensures(stack(s) && result == (*s).head.is_null())]
    unsafe fn is_empty(s: *mut Stack) -> bool
    {
        open stack(s);
        open stack_own(s, head);
        let result = (*s).head.is_null();
        close stack_own(s, head);
        close stack(s);
        return result;
    }

    #[requires(stack(s))]
    #[ensures(stack(s))]
    unsafe fn push(s: *mut Stack, value: i32)
    {
        open stack(s);
        open stack_own(s, old_head);
        let layout = Layout::new::<Node>();
        let n = alloc(layout) as *mut Node;
        if n.is_null() {
            handle_alloc_error(layout);
        }
        (*n).next = (*s).head;
        (*n).value = value;
        close node_own(n, value, old_head);
        close nodes(n);
        (*s).head = n;
        close stack_own(s, n);
        close stack(s);
    }

    #[requires(stack(s) && (*s).head != 0)]
    #[ensures(stack(s))]
    unsafe fn pop(s: *mut Stack) -> i32
    {
        open stack(s);
        open stack_own(s, head);
        open nodes(head);
        open node_own(head, v, next);
        let result = (*head).value;
        (*s).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        close stack_own(s, next);
        close stack(s);
        return result;
    }
    
    #[requires(stack(s))]
    #[ensures(true)]
    unsafe fn dispose(s: *mut Stack)
    {
        open stack(s);
        open stack_own(s, head);
        dispose_nodes(head);
        dealloc(s as *mut u8, Layout::new::<Stack>());
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