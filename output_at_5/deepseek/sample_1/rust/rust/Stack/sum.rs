use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
predicate nodes(nodes: *mut Node; vs: seq<i32>) =
    if (nodes as usize == 0) {
        vs == []
    } else {
        alloc_block(nodes, std::mem::size_of::<Node>()) &*&
        struct_Node_padding(nodes) &*&
        (*nodes).next |-> ?next &*&
        (*nodes).value |-> ?v &*&
        nodes(next, ?vs_tail) &*&
        vs == cons(v, vs_tail)
    };

predicate stack(stack: *mut Stack; vs: seq<i32>) =
    alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> ?head &*&
    nodes(head, vs);
@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes(nodes, ?vs);
//@ ens nodes(nodes, vs) &*& result == sum(vs);
{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open nodes(nodes, vs);
        //@ assert vs == cons(?v, ?vs_tail);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close nodes(nodes, vs);
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, []);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(std::ptr::null_mut(), []);
        //@ close stack(stack, []);
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, vs) &*& result == (vs == []);
    {
        //@ open stack(stack, vs);
        let head = (*stack).head;
        //@ open nodes(head, vs);
        let result = (*stack).head.is_null();
        //@ close nodes(head, vs);
        //@ close stack(stack, vs);
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, vs) &*& result == sum(vs);
    {
        //@ open stack(stack, vs);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack, vs);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, cons(value, vs));
    {
        //@ open stack(stack, vs);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes(n, cons(value, vs));
        (*stack).head = n;
        //@ close stack(stack, cons(value, vs));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, ?vs) &*& vs != [];
    //@ ens stack(stack, tail(vs)) &*& result == head(vs);
    {
        //@ open stack(stack, vs);
        //@ assert vs == cons(?v, ?vs_tail);
        let head = (*stack).head;
        //@ open nodes(head, vs);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, vs_tail);
        result
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, ?vs);
    //@ ens true;
    {
        //@ open stack(stack, vs);
        let mut n = (*stack).head;
        loop {
            //@ invariant nodes(n, ?rem);
            if n.is_null() {
                break;
            }
            //@ open nodes(n, rem);
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        //@ open nodes(std::ptr::null_mut(), _);
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