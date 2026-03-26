use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred] struct NodePred {
    next: *mut Node,
    value: i32,
}

#[pred] struct StackPred {
    head: *mut Node,
}

#[lemma]
fn node_pred_own(n: *mut Node) -> bool
where
    n != std::ptr::null_mut(),
{
    // Ownership of a single Node with full permission
    true
}

#[lemma]
fn stack_pred_own(s: *mut Stack) -> bool
where
    s != std::ptr::null_mut(),
{
    true
}

impl Stack {
    unsafe fn create() -> *mut Stack {
        #[requires(Layout::new::<Stack>().size() > 0)]
        #[ensures(result != std::ptr::null_mut() && 
                 exists<StackPred>(p) ==>
                 p.head == std::ptr::null_mut() &&
                 points_to(result, p) &&
                 owns(result, p))]
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32) {
        #[requires(stack != std::ptr::null_mut() &&
                   exists<StackPred>(p) ==>
                   points_to(stack, p) &&
                   owns(stack, p) &&
                   p.head |-> ?old_head &&
                   (old_head == std::ptr::null_mut() || 
                    (exists<NodePred>(q) ==>
                     points_to(old_head, q) &&
                     owns(old_head, q))))
        #[ensures(exists<StackPred>(p) ==>
                 points_to(stack, p) &&
                 owns(stack, p) &&
                 p.head |-> ?new_head &&
                 (new_head != std::ptr::null_mut() &&
                  exists<NodePred>(n) ==>
                  points_to(new_head, n) &&
                  owns(new_head, n) &&
                  n.value == value &&
                  n.next == ?old_head))]
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32 {
        #[requires(stack != std::ptr::null_mut() &&
                   exists<StackPred>(p) ==>
                   points_to(stack, p) &&
                   owns(stack, p) &&
                   p.head != std::ptr::null_mut() &&
                   exists<NodePred>(n) ==>
                   points_to(p.head, n) &&
                   owns(p.head, n))]
        #[ensures(result == ?v &&
                 exists<StackPred>(p) ==>
                 points_to(stack, p) &&
                 owns(stack, p) &&
                 p.head == ?old_next &&
                 (old_next == std::ptr::null_mut() ||
                  (exists<NodePred>(q) ==>
                   points_to(old_next, q) &&
                   owns(old_next, q))) &&
                 !owns(?old_head, ?n))]
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack) {
        #[requires(stack != std::ptr::null_mut() &&
                   exists<StackPred>(p) ==>
                   points_to(stack, p) &&
                   owns(stack, p) &&
                   p.head == std::ptr::null_mut())]
        #[ensures(true)]
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