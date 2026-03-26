use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(struct Node* node; list<int> vs) =
    if node == std::ptr::null_mut() {
        emp
    } else
        node |-> struct Node { next: *mut Node, value: int } &*&
        node->next |-> ?next &*& node->value |-> ?v &*&
        nodes(next, ?rest) &*& vs == cons(v, rest);

predicate stack(struct Stack* stack; list<int> vs) =
    stack |-> struct Stack { head: *mut Node } &*&
    stack->head |-> ?head &*& nodes(head, vs);

#[requires(true)]
#[ensures(result != std::ptr::null_mut() &*& stack(result, nil))]
unsafe fn create() -> *mut Stack
{
    let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
    if stack.is_null() {
        handle_alloc_error(Layout::new::<Stack>());
    }
    (*stack).head = std::ptr::null_mut();

    stack
}

#[requires(stack(s, ?vs))]
#[ensures(stack(s, vs) &*& result == sum(vs))]
unsafe fn get_sum(stack: *mut Stack) -> i32
{
    #[predicate]
    #[public]
    fn sum(list<int> vs) -> int {
        switch(vs) {
            case nil: 0
            case cons(h, t): h + sum(t)
        }
    }

    unsafe fn get_nodes_sum(node: *mut Node)
        #[requires(nodes(node, ?vs))]
        #[ensures(nodes(node, vs) &*& result == sum(vs))]
        -> i32
    {
        let mut result = 0;
        if !node.is_null() {
            let tail_sum = get_nodes_sum((*node).next);
            result = (*node).value + tail_sum;
        }
        result
    }

    let result = get_nodes_sum((*stack).head);
    result
}

#[requires(stack(s, vs))]
#[ensures(stack(s, cons(value, vs)))]
unsafe fn push(stack: *mut Stack, value: i32)
{
    let n = alloc(Layout::new::<Node>()) as *mut Node;
    if n.is_null() {
        handle_alloc_error(Layout::new::<Node>());
    }

    (*n).next = (*stack).head;
    (*n).value = value;
    (*stack).head = n;
}

#[requires(stack(s, cons(v, vs)))]
#[ensures(stack(s, vs) &*& result == v)]
unsafe fn pop(stack: *mut Stack) -> i32
{
    let head = (*stack).head;
    let result = (*head).value;
    (*stack).head = (*head).next;
    dealloc(head as *mut u8, Layout::new::<Node>());
    result
}

#[requires(stack(s, nil))]
#[ensures(true)]
unsafe fn dispose(stack: *mut Stack)
{
    dealloc(stack as *mut u8, Layout::new::<Stack>());
}

fn main()
{
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