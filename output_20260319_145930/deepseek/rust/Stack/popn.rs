use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred nodes(n: *mut Node; sum: i32) =
    if n.is_null() {
        sum == 0
    } else {
        alloc_block(n, std::mem::size_of::<Node>()) &*&
        (*n).next |-> next &*&
        (*n).value |-> v &*&
        nodes(next, sum_next) &*&
        sum == v + sum_next
    };
@*/

/*@
pred stack(s: *mut Stack) =
    alloc_block(s, std::mem::size_of::<Stack>()) &*&
    (*s).head |-> head &*&
    nodes(head, _);
@*/

//@ req nodes(nodes, ?sum);
//@ ens nodes(nodes, sum) &*& result == sum;
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open nodes(nodes, _);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close nodes(nodes, result);
    } else {
        //@ open nodes(nodes, _);
        //@ close nodes(nodes, 0);
    }
    
    result
}

impl Stack {
    //@ req true;
    //@ ens stack(result);
    unsafe fn create() -> *mut Stack
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
    
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == (*stack).head.is_null();
    unsafe fn is_empty(stack: *mut Stack) -> bool
    {
        //@ open stack(stack);
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        //@ close stack(stack);
        result
    }
    
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == ?sum &*& nodes((*stack).head, sum);
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        //@ open stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack);
        result
    }

    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes(n, value + ?old_sum);
        (*stack).head = n;
        //@ close stack(stack);
    }

    //@ req stack(stack) &*& (*stack).head != std::ptr::null_mut();
    //@ ens stack(stack) &*& result == ?v;
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        result
    }
    
    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn popn(stack: *mut Stack, n: i32)
    {
        let mut i = 0;
        //@ inv stack(stack);
        loop {
            if i == n {
                break;
            }
            //@ open stack(stack);
            //@ if (*stack).head.is_null() { close stack(stack); } else { close stack(stack); }
            Stack::pop(stack);
            i += 1;
        }
    }
    
    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack);
        let mut n = (*stack).head;
        //@ open nodes(n, _);
        //@ inv nodes(n, _);
        loop {
            if n.is_null() {
                break;
            }
            //@ open nodes(n, _);
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