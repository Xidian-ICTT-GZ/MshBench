use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred]
struct NodePred {
    next: *mut Node,
    value: i32,
    #[ghost] owned: bool,
}

#[pred]
struct StackPred {
    head: *mut Node,
    #[ghost] owned: bool,
}

#[lemma]
fn node_pred_valid(node: *mut Node) -> bool
where
    node != std::ptr::null_mut()
{
    requires([
        node |-> Node { next: ?next, value: ?value },
        NodePred { next: next, value: value, owned: true }
    ]);
    ensures([
        NodePred { next: next, value: value, owned: true }
    ]);
    // trivial lemma for predicate validity
}

#[lemma]
fn stack_pred_valid(stack: *mut Stack) -> bool
where
    stack != std::ptr::null_mut()
{
    requires([
        stack |-> Stack { head: ?head },
        StackPred { head: head, owned: true }
    ]);
    ensures([
        StackPred { head: head, owned: true }
    ]);
}

#[predicate]
fn list_sum(node: *mut Node, sum: i32) {
    (node == std::ptr::null_mut() && sum == 0) ||
    (node != std::ptr::null_mut() &&
     node |-> Node { next: ?next, value: ?val } &&
     NodePred { next: next, value: val, owned: true } &&
     list_sum(next, ?tail_sum) &&
     sum == val + tail_sum)
}

#[predicate]
fn stack_list(stack: *mut Stack, head: *mut Node) {
    stack |-> Stack { head: head } &&
    StackPred { head: head, owned: true }
}

unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    requires([
        node == std::ptr::null_mut() || 
        (node |-> Node { next: ?next, value: ?val } &&
         NodePred { next: next, value: val, owned: true } &&
         list_sum(next, ?tail_sum))
    ]);
    ensures([
        list_sum(node, result)
    ]);
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

impl Stack {
    unsafe fn create() -> *mut Stack {
        requires([]);
        ensures([
            result != std::ptr::null_mut() &&
            result |-> Stack { head: std::ptr::null_mut() } &&
            StackPred { head: std::ptr::null_mut(), owned: true }
        ]);
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        requires([
            stack != std::ptr::null_mut() &&
            stack_list(stack, ?head)
        ]);
        ensures([
            list_sum(head, result)
        ]);
        let result = get_nodes_sum((*stack).head);

        result
    }

    unsafe fn push(stack: *mut Stack, value: i32) {
        requires([
            stack != std::ptr::null_mut() &&
            stack_list(stack, ?old_head)
        ]);
        ensures([
            stack_list(stack, ?new_head) &&
            new_head != std::ptr::null_mut() &&
            new_head |-> Node { next: old_head, value: value } &&
            NodePred { next: old_head, value: value, owned: true }
        ]);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32 {
        requires([
            stack != std::ptr::null_mut() &&
            stack_list(stack, ?head) &&
            head != std::ptr::null_mut() &&
            head |-> Node { next: ?next, value: ?val } &&
            NodePred { next: next, value: val, owned: true }
        ]);
        ensures([
            stack_list(stack, next) &&
            result == val &&
            // after deallocation, the node is no longer owned
            // but we ensure the heap is clean
        ]);
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack) {
        requires([
            stack != std::ptr::null_mut() &&
            stack_list(stack, ?head) &&
            (head == std::ptr::null_mut() ||
             (head |-> Node { next: ?next, value: ?val } &&
              NodePred { next: next, value: val, owned: true } &&
              list_sum(head, ?sum)))
        ]);
        ensures([]);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let sum = Stack::get_sum(s);

        let result1 = Stack::pop(s);

        let result2 = Stack::pop(s);

        Stack::dispose(s);
    }
}