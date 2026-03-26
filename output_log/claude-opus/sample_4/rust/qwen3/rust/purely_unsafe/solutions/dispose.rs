use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
pub struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
pub struct Stack {
    head: *mut Node,
}

#[predicate]
fn NodePred(n: *mut Node, next: *mut Node, value: i32, owned: bool) = 
    owned == true ?
        n != std::ptr::null_mut() &*& 
        n->Node { next: next, value: value }
    :
        n != std::ptr::null_mut() &*&
        (true); 
        // Must mention heap ownership in predicate bodies; the false case typically owns nothing, 
        // but VeriFast requires body refers to heap, and "owned==false" is used only as a ghost flag

#[predicate]
fn StackPred(s: *mut Stack, head: *mut Node, owned: bool) =
    owned == true ?
        s != std::ptr::null_mut() &*& 
        s->Stack { head: head } &*& nodes_list(head)
    :
        s != std::ptr::null_mut() &*& 
        s->Stack { head: head };

#[predicate_family]
fn nodes_list(n: *mut Node) =
    n == std::ptr::null_mut() ? emp : NodePred(n, (*n).next, (*n).value, true) &*& nodes_list((*n).next);

#[lemma]
fn node_pred_dispose(n: *mut Node)
    requires
        NodePred(n, ?next, ?value, true) &*& nodes_list(next)
    ensures
        NodePred(n, next, value, false) &*& nodes_list(next)
{
}

#[lemma]
fn stack_pred_dispose(s: *mut Stack)
    requires
        StackPred(s, ?head, true)
    ensures
        StackPred(s, head, false)
{
}

impl Stack {
    #[requires(
        Layout::new::<Stack>().size() > 0 &&
        Layout::new::<Stack>().align() > 0
    )]
    #[ensures(
        result != std::ptr::null_mut() &&
        StackPred(result, std::ptr::null_mut(), true)
    )]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(
        StackPred(stack, ?head, true)
    )]
    #[ensures(
        StackPred(stack, head, true) &*&
        result == (head == std::ptr::null_mut())
    )]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        (*stack).head.is_null()
    }

    #[requires(
        StackPred(stack, ?old_head, true) &&
        Layout::new::<Node>().size() > 0 &&
        Layout::new::<Node>().align() > 0
    )]
    #[ensures(
        StackPred(stack, ?new_head, true) &*&
        NodePred(new_head, old_head, value, true) &*&
        nodes_list(old_head)
    )]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(
        StackPred(stack, ?head, true) &*&
        head != std::ptr::null_mut() &*&
        NodePred(head, ?next, ?value, true) &*&
        nodes_list(next)
    )]
    #[ensures(
        StackPred(stack, next, true) &*&
        nodes_list(next) &*&
        result == value
    )]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(
        StackPred(stack, ?head, true) &*&
        nodes_list(head)
    )]
    #[ensures(
        emp
    )]
    unsafe fn dispose(stack: *mut Stack) {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[requires(
    n != std::ptr::null_mut() &*&
    NodePred(n, ?next, ?value, true) &*&
    nodes_list(next)
)]
#[ensures(
    emp
)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}