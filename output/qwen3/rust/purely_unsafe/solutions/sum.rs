use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred]
struct NodePred {
    next: *mut Node,
    value: i32,
    #[ghost] inv: bool,
}

#[pred]
struct StackPred {
    head: *mut Node,
    #[ghost] inv: bool,
}

#[lemma]
fn node_pred_inv(n: *mut Node) -> bool
where
    n != 0,
    NodePred { next: (*n).next, value: (*n).value, inv: true }
{
    true
}

#[lemma]
fn stack_pred_inv(s: *mut Stack) -> bool
where
    s != 0,
    StackPred { head: (*s).head, inv: true }
{
    true
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    #[requires(nodes == 0 || NodePred { next: (*nodes).next, value: (*nodes).value, inv: true })]
    #[ensures(result == if nodes == 0 { 0 } else { (*nodes).value + get_nodes_sum((*nodes).next) })]
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
        #[ensures(result != 0 && StackPred { head: std::ptr::null_mut(), inv: true })]
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool {
        #[requires(stack != 0 && StackPred { head: (*stack).head, inv: true })]
        #[ensures(result == ((*stack).head == 0))]
        let head = (*stack).head;

        let result = (*stack).head.is_null();

        result
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        #[requires(stack != 0 && StackPred { head: (*stack).head, inv: true })]
        #[ensures(result == get_nodes_sum((*stack).head))]
        let result = get_nodes_sum((*stack).head);

        result
    }

    unsafe fn push(stack: *mut Stack, value: i32) {
        #[requires(stack != 0 && StackPred { head: (*stack).head, inv: true })]
        #[ensures(StackPred { head: (*stack).head, inv: true })]
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32 {
        #[requires(stack != 0 && StackPred { head: (*stack).head, inv: true } && (*stack).head != 0)]
        #[ensures(StackPred { head: (*stack).head, inv: true } && result == (*(*stack).head).value)]
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack) {
        #[requires(stack != 0 && StackPred { head: (*stack).head, inv: true })]
        #[ensures(true)]
        let mut n = (*stack).head;
        loop {
            #[invariant(
                n == 0 ||
                (n != 0 &&
                 NodePred { next: (*n).next, value: (*n).value, inv: true } &&
                 StackPred { head: (*stack).head, inv: true })
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