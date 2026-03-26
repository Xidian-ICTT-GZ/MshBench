use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(n: *mut Node; sum: int) =
    n == null ?
        sum == 0
    :
        n->next |-> ?next &*&
        n->value |-> ?v &*&
        nodes(next, ?rest_sum) &*&
        sum == v + rest_sum;

predicate stack(s: *mut Stack; sum: int) =
    s->head |-> ?h &*&
    nodes(h, sum);

#[requires(nodes(nodes, ?sum))]
#[ensures(nodes(nodes, sum) &*& result == sum)]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
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

    #[requires(stack(stack, ?sum))]
    #[ensures(stack(stack, sum) &*& result == (sum == 0))]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        let head = (*stack).head;

        let result = (*stack).head.is_null();

        result
    }

    #[requires(stack(stack, ?sum))]
    #[ensures(stack(stack, sum) &*& result == sum)]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }

    #[requires(stack(stack, ?sum))]
    #[ensures(stack(stack, sum + value))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, ?sum) &*& sum != 0)]
    #[ensures(stack(stack, sum - result))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        head->next |-> ?next &*& head->value |-> ?v &*& nodes(next, ?rest_sum) &*& stack(stack, v + rest_sum);

        (*stack).head = next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        v
    }

    #[requires(stack(stack, ?sum) &*& n >= 0)]
    #[ensures(stack(stack, ?new_sum) &*& new_sum <= sum)]
    unsafe fn popn(stack: *mut Stack, n: i32) {
        let mut i = 0;
        #[invariant(stack(stack, ?cur_sum) &*& 0 <= i &*& i <= n)]
        loop {
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }

    #[requires(stack(stack, ?sum))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        let mut n = (*stack).head;
        #[invariant(nodes(n, ?cur_sum))]
        loop {
            if n.is_null() {
                break;
            }

            n->next |-> ?next &*& n->value |-> _ &*& nodes(next, ?rest_sum) &*& nodes(n, cur_sum);
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