use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

/*@
predicate node(struct Node* n; int val, struct Node* next) =
    n->value |-> val &*& n->next |-> next;
predicate nodes(struct Node* n; list<int> vs) =
    n == 0 ? vs == nil :
    node(n, head(vs), ?nextNode) &*& nodes(nextNode, tail(vs));
@*/

struct Stack {
    head: *mut Node,
}

/*@
predicate stack(struct Stack* s; list<int> vs) =
    s->head |-> ?headPtr &*& nodes(headPtr, vs);
@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ requires nodes == std::ptr::null_mut() ? true : node(nodes, ?val, ?next);
//@ ensures nodes == std::ptr::null_mut() ? result == 0 : result == val + old(get_nodes_sum(next));
{
    let mut result = 0;

    if !nodes.is_null() {
        //@ open node(nodes, ?val, ?next);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close node(nodes, val, next);
    }

    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        //@ close stack(stack, nil);
        stack
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ requires stack(stack, ?vs);
    //@ ensures stack(stack, vs) &*& result == (vs == nil);
    {
        //@ open stack(stack, vs);
        let head = (*stack).head;

        let result = (*stack).head.is_null();

        //@ close stack(stack, vs);
        result
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?vs);
    //@ ensures stack(stack, vs) &*& result == fold_left(|acc,i| acc+i, 0, vs);
    {
        //@ open stack(stack, vs);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack, vs);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack, ?vs);
    //@ ensures stack(stack, cons(value, vs));
    {
        //@ open stack(stack, vs);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;

        //@ close node(n, value, (*stack).head);
        //@ close stack(stack, cons(value, vs));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?vs) &*& vs != nil;
    //@ ensures stack(stack, tail(vs)) &*& result == head(vs);
    {
        //@ open stack(stack, vs);
        let head = (*stack).head;
        //@ open node(head, ?val, ?next);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, tail(vs));
        result
    }

    unsafe fn popn(stack: *mut Stack, n: i32)
    //@ requires stack(stack, ?vs) &*& length(vs) >= n as nat &*& n >= 0;
    //@ ensures stack(stack, drop(n as nat, vs));
    {
        //@ open stack(stack, vs);
        let mut i = 0;
        loop {
            //@ invariant stack(stack, ?vs0) &*& length(vs0) == length(vs) - i as nat &*& i as nat <= n as nat;
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
        //@ close stack(stack, drop(n as nat, vs));
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack, ?vs);
    //@ ensures true;
    {
        //@ open stack(stack, vs);
        let mut n = (*stack).head;
        loop {
            if n.is_null() {
                break;
            }
            //@ open node(n, _, _);
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }

        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}