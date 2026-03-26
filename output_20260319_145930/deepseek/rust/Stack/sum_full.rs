use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred nodes(node: *mut Node; vs: list<i32>) =
    if node.is_null() {
        vs == []
    } else {
        alloc_block(node, std::mem::size_of::<Node>()) &*&
        (*node).value |-> ?v &*&
        (*node).next |-> ?next &*&
        nodes(next, ?tail) &*&
        vs == cons(v, tail)
    };

pred stack(stack: *mut Stack) =
    alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    (*stack).head |-> ?head &*&
    nodes(head, _);
@*/

//@ req nodes(node, ?vs);
//@ ens nodes(node, vs) &*& result == sum(vs);
unsafe fn get_nodes_sum(node: *mut Node) -> i32
{
    //@ open nodes(node, _);
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes(node, _);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close nodes(node, _);
    } else {
        //@ close nodes(node, _);
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
        //@ close nodes(std::ptr::null_mut(), _);
        //@ close stack(stack);
        stack
    }
    
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == ?sum;
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
        //@ close nodes(n, cons(value, ?old_vs));
        //@ open nodes((*stack).head, old_vs);
        (*stack).head = n;
        //@ close stack(stack);
    }
    
    //@ req stack(stack) &*& (*stack).head |-> ?head &*& head != std::ptr::null_mut();
    //@ ens stack(stack) &*& result == ?v;
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open nodes((*head).next, _);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        result
    }

    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack);
        //@ open nodes((*stack).head, _);
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
        //@ assert sum == 30;
        let result1 = Stack::pop(s);
        //@ assert result1 == 20;
        let result2 = Stack::pop(s);
        //@ assert result2 == 10;
        Stack::dispose(s);
    }
}