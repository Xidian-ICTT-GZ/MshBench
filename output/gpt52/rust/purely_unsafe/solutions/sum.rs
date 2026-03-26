use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate node(struct Node *n; struct Node *next, i32 value) =
    n->next |-> next &*& n->value |-> value;

predicate nodes(struct Node *n) =
    n == 0 ?
        emp
    :
        node(n, ?next, ?value) &*& nodes(next);

predicate stack(struct Stack *s) =
    s->head |-> ?h &*& nodes(h);

@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    //@ requires nodes(nodes);
    //@ ensures nodes(nodes) &*& true;
{
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    unsafe fn create() -> *mut Stack
        //@ requires emp;
        //@ ensures stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(0);
        //@ close stack(stack);

        stack
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
        //@ requires stack(stack);
        //@ ensures stack(stack) &*& true;
    {
        //@ open stack(stack);
        let head = (*stack).head;

        let result = (*stack).head.is_null();

        //@ close stack(stack);
        result
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
        //@ requires stack(stack);
        //@ ensures stack(stack) &*& true;
    {
        //@ open stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack);

        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        //@ requires stack(stack);
        //@ ensures stack(stack);
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n, (*n).next, value);
        //@ close nodes(n);
        //@ close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        //@ requires stack(stack) &*& nodes((*stack).head) &*& (*stack).head != 0;
        //@ ensures stack(stack) &*& true;
    {
        //@ open stack(stack);
        //@ open nodes((*stack).head);
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open node(head, ?next, ?value0);
        //@ close nodes((*stack).head);
        //@ close stack(stack);
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack)
        //@ requires stack(stack);
        //@ ensures emp;
    {
        //@ open stack(stack);
        let mut n = (*stack).head;
        //@ open nodes(n);
        loop {
            //@ invariant stack->head |-> ?h &*& nodes(n);
            if n.is_null() {
                break;
            }

            //@ open nodes(n);
            let next = (*n).next;
            //@ open node(n, next, ?v);
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        //@ close nodes(0);
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