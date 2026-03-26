use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ predicate nodes(nodes: *mut Node; result: i32) = nodes == 0 ? result == 0 : (*nodes).next |-> ?next &*& (*nodes).value |-> ?v &*& nodes(next, ?s) &*& result == v + s;

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes(nodes, ?sum);
//@ ens nodes(nodes, sum) &*& result == sum;
{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open nodes(nodes, sum);
        result = get_nodes_sum((*nodes).next);
        //@ open nodes((*nodes).next, ?subsum);
        result += (*nodes).value;
        //@ close nodes((*nodes).next, subsum);
        //@ close nodes(nodes, sum);
    } else {
        //@ open nodes(nodes, sum);
        //@ close nodes(nodes, sum);
    }
    
    result
}

impl Stack {
    //@ predicate stack(stack: *mut Stack) = (*stack).head |-> ?head &*& nodes(head, _);

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(std::ptr::null_mut(), 0);
        //@ close stack(stack);
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == ((*stack).head == 0);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        //@ close stack(stack);
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes(n, value + ?oldsum);
        (*stack).head = n;
        //@ close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head, ?sum);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        result
    }
    
    unsafe fn popn(stack: *mut Stack, n: i32)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        let mut i = 0;
        loop {
            //@ invariant stack(stack) &*& 0 <= i &*& i <= n;
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        let mut n = (*stack).head;
        loop {
            //@ invariant nodes(n, _);
            if n.is_null() {
                break;
            }
            //@ open nodes(n, _);
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        //@ open nodes(std::ptr::null_mut(), _);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
//@ req true;
//@ ens true;
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