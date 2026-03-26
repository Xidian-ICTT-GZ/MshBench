use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred]
pub unsafe fn nodes_list(n: *mut Node) = 
    n == std::ptr::null_mut()
    ? emp
    : NodePred { next: (*n).next, value: (*n).value, inv: true } * nodes_list((*n).next);

#[pred]
pub unsafe fn NodePred(n: *mut Node) = 
    exists (next: *mut Node, value: i32) (
        n != std::ptr::null_mut() &*&
        n->next |-> next &*&
        n->value |-> value &*&
        nodes_list(next)
    );

#[pred]
pub unsafe fn StackPred(s: *mut Stack) = 
    s != std::ptr::null_mut() &*& s->head |-> ?head &*& nodes_list(head);

#[lemma]
#[requires(n != std::ptr::null_mut() &*& NodePred(n))]
#[ensures(true)]
fn node_pred_inv(n: *mut Node) {
}

#[lemma]
#[requires(s != std::ptr::null_mut() &*& StackPred(s))]
#[ensures(true)]
fn stack_pred_inv(s: *mut Stack) {
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    #[requires(nodes == std::ptr::null_mut() || NodePred(nodes))]
    #[ensures(result == (if nodes == std::ptr::null_mut() { 0 } else { (*nodes).value + get_nodes_sum((*nodes).next) }))]
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    unsafe fn create() -> *mut Stack {
        #[requires(true)]
        #[ensures(result != std::ptr::null_mut() && StackPred(result))]
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool {
        #[requires(StackPred(stack))]
        #[ensures(result == ((*stack).head == std::ptr::null_mut()))]
        let head = (*stack).head;

        let result = (*stack).head.is_null();

        result
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        #[requires(StackPred(stack))]
        #[ensures(result == get_nodes_sum((*stack).head))]
        let result = get_nodes_sum((*stack).head);

        result
    }

    unsafe fn push(stack: *mut Stack, value: i32) {
        #[requires(StackPred(stack))]
        #[ensures(StackPred(stack))]
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32 {
        #[requires(StackPred(stack) && (*stack).head != std::ptr::null_mut())]
        #[ensures(StackPred(stack) && result == (*old((*stack).head)).value)]
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack) {
        #[requires(StackPred(stack))]
        #[ensures(emp)]
        let mut n = (*stack).head;
        loop {
            #[invariant(
                StackPred(stack) &*&
                (n == std::ptr::null_mut() || NodePred(n))
            )]
            if n.is_null() {
                break;
            }

            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }

        dealloc(stack as *mut u8, Layout::new::<Stack>());
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