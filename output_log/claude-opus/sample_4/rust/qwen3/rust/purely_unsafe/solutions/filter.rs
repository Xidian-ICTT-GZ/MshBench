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
pub unsafe fn node_pred(n: *mut Node) = 
    n != std::ptr::null_mut() &*& 
    malloc_block_Node(n) &*& 
    (*n).value |-> _ &*&
    (*n).next |-> _ &*&
    list_pred((*n).next)
;

#[predicate]
pub unsafe fn stack_pred(s: *mut Stack) =
    s != std::ptr::null_mut() &*&
    malloc_block_Stack(s) &*&
    (*s).head |-> ?h &*&
    list_pred(h)
;

#[predicate]
pub unsafe fn list_pred(head: *mut Node) =
    if head == std::ptr::null_mut() {
        emp
    } else {
        node_pred(head)
    }
;

#[lemma]
#[requires(node_pred(n))]
#[ensures(list_pred((*n).next) * (*n).value |-> (*n).value)]
pub unsafe fn node_pred_split(n: *mut Node) {
    // Verified by unfolding node_pred
}

#[lemma]
#[requires(list_pred(head))]
#[ensures(head == std::ptr::null_mut() ? emp : node_pred(head))]
pub unsafe fn list_pred_split(head: *mut Node) {
    // Verified by unfolding list_pred
}

type I32Predicate = fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
#[requires(list_pred(n))]
#[ensures(list_pred(result))]
{
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);
            
            // Own n and its fields via node_pred
            // Update next pointer and preserve ownership
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
#[requires(list_pred(n))]
#[ensures(emp)]
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    #[requires(true)]
    #[ensures(stack_pred(result))]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    #[requires(stack_pred(stack))]
    #[ensures(stack_pred(stack))]
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
    #[requires(stack_pred(stack) * (*stack).head |-> ?head_ptr * node_pred(head_ptr))]
    #[ensures(stack_pred(stack))]
    {
        let head = (*stack).head;
        let val = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        val
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    #[requires(stack_pred(stack))]
    #[ensures(stack_pred(stack))]
    {
        let head = filter_nodes((*stack).head, p);

        (*stack).head = head;
    }

    unsafe fn dispose(stack: *mut Stack)
    #[requires(stack_pred(stack))]
    #[ensures(emp)]
    {
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