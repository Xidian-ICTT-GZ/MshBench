use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn nodes(nodes: *mut Node) -> bool {
    if nodes.is_null() {
        true
    } else {
        let node = unsafe { &*nodes };
        nodes(node.next) && true
    }
}

#[predicate]
fn nodes_sum(nodes: *mut Node, sum: i32) -> bool {
    if nodes.is_null() {
        sum == 0
    } else {
        let node = unsafe { &*nodes };
        exists!(next_sum: i32 | nodes_sum(node.next, next_sum) && sum == next_sum + node.value)
    }
}

#[predicate]
fn stack(stack: *mut Stack) -> bool {
    if stack.is_null() {
        false
    } else {
        let s = unsafe { &*stack };
        nodes(s.head) && true
    }
}

#[predicate]
fn stack_sum(stack: *mut Stack, sum: i32) -> bool {
    if stack.is_null() {
        false
    } else {
        let s = unsafe { &*stack };
        nodes_sum(s.head, sum) && true
    }
}

#[predicate]
fn node_full(node: *mut Node) -> bool {
    !node.is_null() && true
}

#[predicate]
fn stack_full(stack: *mut Stack) -> bool {
    !stack.is_null() && true
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 
    #[requires(nodes(nodes))]
    #[ensures(nodes_sum(nodes, result))]
{
    let mut result = 0;

    if !nodes.is_null() {
        let node = &*nodes;
        result = get_nodes_sum(node.next);
        result += node.value;
    }

    result
}

impl Stack {
    unsafe fn create() -> *mut Stack 
        #[ensures(stack_full(result) && stack(result))]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool 
        #[requires(stack_full(stack) && stack(stack))]
        #[ensures(stack_full(stack) && stack(stack))]
    {
        let head = (*stack).head;

        let result = (*stack).head.is_null();

        result
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32 
        #[requires(stack_full(stack) && stack(stack))]
        #[ensures(stack_full(stack) && stack_sum(stack, result))]
    {
        let result = get_nodes_sum((*stack).head);

        result
    }

    unsafe fn push(stack: *mut Stack, value: i32) 
        #[requires(stack_full(stack) && stack(stack))]
        #[ensures(stack_full(stack) && stack(stack))]
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
        #[requires(stack_full(stack) && stack(stack) && !(*stack).head.is_null())]
        #[ensures(stack_full(stack) && stack(stack))]
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn popn(stack: *mut Stack, n: i32) 
        #[requires(stack_full(stack) && stack(stack))]
        #[ensures(stack_full(stack) && stack(stack))]
    {
        let mut i = 0;
        #[invariant(stack_full(stack) && stack(stack))]
        loop {
            if i == n {
                break;
            }
            if (*stack).head.is_null() {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }

    unsafe fn dispose(stack: *mut Stack) 
        #[requires(stack_full(stack) && stack(stack))]
        #[ensures(true)]
    {
        let mut n = (*stack).head;
        #[invariant(nodes(n))]
        loop {
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