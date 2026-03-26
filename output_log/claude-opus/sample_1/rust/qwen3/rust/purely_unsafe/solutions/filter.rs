use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
pub struct Node {
    pub value: i32,
    pub next: *mut Node,
}

#[repr(C)]
pub struct Stack {
    pub head: *mut Node,
}

#[predicate]
pub predicate node_pred(n: *mut Node) = 
    n != std::ptr::null_mut() &*& 
    malloc_block_Node(n) &*&
    (*n).value |-> _ &*&
    (*n).next |-> _ &*&
    true

#[predicate]
pub predicate list_pred(head: *mut Node) = 
    head == std::ptr::null_mut() ? emp : 
    node_pred(head) &*& list_pred((*head).next)

#[predicate]
pub predicate stack_pred(s: *mut Stack) = 
    s != std::ptr::null_mut() &*& 
    malloc_block_Stack(s) &*&
    (*s).head |-> ?head &*& list_pred(head)

#[lemma]
fn node_pred_split(n: *mut Node)
    requires node_pred(n),
    ensures (*n).value |-> _ &*& (*n).next |-> _ &*& malloc_block_Node(n)
{
    open node_pred(n);
    close node_pred(n);
}

#[lemma]
fn list_pred_split(head: *mut Node)
    requires list_pred(head),
    ensures head == std::ptr::null_mut() ? emp : (node_pred(head) &*& list_pred((*head).next))
{
    open list_pred(head);
    close list_pred(head);
}

unsafe fn filter_nodes(n: *mut Node, p: fn(i32) -> bool) -> *mut Node
#[requires list_pred(n)]
#[ensures list_pred(result)]
{
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        open list_pred(n);
        open node_pred(n);
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);
            (*n).next = next;
            close node_pred(n);
            close list_pred(n);
            n
        } else {
            next = (*n).next;
            close list_pred(next);
            close node_pred(n);
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            close list_pred(result);
            result
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
#[requires list_pred(n)]
#[ensures emp]
{
    if !n.is_null() {
        open list_pred(n);
        open node_pred(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    #[requires emp]
    #[ensures stack_pred(result)]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        close list_pred(std::ptr::null_mut());
        (*stack).head = std::ptr::null_mut();
        close stack_pred(stack);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    #[requires stack_pred(stack)]
    #[ensures stack_pred(stack)]
    {
        open stack_pred(stack);
        open list_pred((*stack).head);
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).value = value;
        (*n).next = (*stack).head;
        close node_pred(n);
        close list_pred(n);
        (*stack).head = n;
        close stack_pred(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    #[requires stack_pred(stack) &*& (*stack).head != std::ptr::null_mut()]
    #[ensures stack_pred(stack)]
    {
        open stack_pred(stack);
        let head = (*stack).head;
        open list_pred(head);
        open node_pred(head);

        let result = (*head).value;
        (*stack).head = (*head).next;
        close list_pred((*stack).head);
        dealloc(head as *mut u8, Layout::new::<Node>());
        close stack_pred(stack);
        result
    }

    unsafe fn filter(stack: *mut Stack, p: fn(i32) -> bool)
    #[requires stack_pred(stack)]
    #[ensures stack_pred(stack)]
    {
        open stack_pred(stack);
        let head = filter_nodes((*stack).head, p);
        (*stack).head = head;
        close stack_pred(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
    #[requires stack_pred(stack)]
    #[ensures emp]
    {
        open stack_pred(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool {
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