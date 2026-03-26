use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

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

predicate nodes(struct Node *n; i32 sum) =
    n == 0 ?
        sum == 0
    :
        node(n, ?next, ?value) &*& nodes(next, ?tail_sum) &*& sum == value + tail_sum;

predicate stack(struct Stack *s; i32 sum) =
    s->head |-> ?h &*& nodes(h, sum);

@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ requires nodes(node, ?sum);
//@ ensures nodes(node, sum) &*& result == sum;
{
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result, 0);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        //@ close nodes(0, 0);
        //@ close stack(stack, 0);
        stack
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?sum);
    //@ ensures stack(stack, sum) &*& result == sum;
    {
        //@ open stack(stack, sum);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack, sum);

        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack, ?sum);
    //@ ensures stack(stack, sum + value);
    {
        //@ open stack(stack, sum);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n, (*stack).head, value);
        //@ close nodes(n, value + sum);
        (*stack).head = n;
        //@ close stack(stack, sum + value);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?sum) &*& sum != 0;
    //@ ensures stack(stack, sum - result);
    {
        //@ open stack(stack, sum);
        let head = (*stack).head;

        //@ open nodes(head, sum);
        //@ open node(head, ?next, ?value);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, sum - result);

        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack, 0);
    //@ ensures true;
    {
        //@ open stack(stack, 0);
        //@ open nodes((*stack).head, 0);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
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