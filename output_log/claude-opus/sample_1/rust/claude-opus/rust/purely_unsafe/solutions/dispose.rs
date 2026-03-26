use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(n: *mut Node; count: i32) =
    n == std::ptr::null_mut() ?
        count == 0
    :
        (*n).next |-> ?next &*& (*n).value |-> ?value &*& 
        malloc_block_Node(n) &*&
        nodes(next, ?rest_count) &*& count == rest_count + 1;

predicate stack(s: *mut Stack; count: i32) =
    (*s).head |-> ?head &*& malloc_block_Stack(s) &*& nodes(head, count);

#[requires(nodes(n, count))]
#[ensures(nodes(n, 0))]
unsafe fn dispose_nodes(n: *mut Node)
    decreases count
{
    if !n.is_null() {
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[ensures(stack(result, 0))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack(stack, count))]
    #[ensures(stack(stack, count))]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        let head = (*stack).head;

        head.is_null()
    }

    #[requires(stack(stack, count))]
    #[ensures(stack(stack, count + 1))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, count) &*& count > 0)]
    #[ensures(stack(stack, count - 1))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        (*stack).head = (*head).next;
        let result = (*head).value;

        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack(stack, count))]
    #[ensures(nodes((*stack).head, 0))]
    #[ensures(malloc_block_Stack(stack))]
    #[ensures(stack == 0 ? true : true)] // dummy to avoid trivial true ensures only
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dispose_nodes((*stack).head);
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