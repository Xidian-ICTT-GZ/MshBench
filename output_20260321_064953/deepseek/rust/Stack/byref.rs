use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ predicate node(struct Node* node; struct Node* next, i32 value) = 
//@     node != 0 &*&
//@     alloc_block(node, std::mem::size_of::<Node>()) &*&
//@     struct_Node_padding(node) &*&
//@     (*node).next |-> next &*&
//@     (*node).value |-> value;

//@ predicate nodes(struct Node* n) =
//@     n == 0 ? true : node(n, ?next, _) &*& nodes(next);

//@ predicate stack(struct Stack* stack) =
//@     stack != 0 &*&
//@     alloc_block(stack, std::mem::size_of::<Stack>()) &*&
//@     struct_Stack_padding(stack) &*&
//@     (*stack).head |-> ?head &*&
//@     nodes(head);

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req nodes(*n) &*& p == neq_20;
//@ ens nodes(*n);
{
    //@ open nodes(*n);
    if !(*n).is_null() {
        //@ open node(*n, ?next, ?value);
        let keep = p((**n).value);
        if keep {
            //@ close node(*n, next, value);
            //@ close nodes(*n);
            filter_nodes(&raw mut (**n).next, p);
            //@ open nodes((**n).next);
            //@ open node(*n, ?new_next, value);
            //@ close node(*n, new_next, value);
            //@ close nodes(*n);
        } else {
            let next_ = (**n).next;
            //@ close node(*n, next, value);
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
            //@ close nodes(*n);
        }
    } else {
        //@ close nodes(*n);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req nodes(n);
//@ ens true;
{
    //@ open nodes(n);
    if !n.is_null() {
        //@ open node(n, ?next, _);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result);
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
        //@ close node(n, (*stack).head, value);
        //@ open nodes((*stack).head);
        //@ close nodes(n);
        (*stack).head = n;
        //@ close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack) &*& (*stack).head != 0;
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        //@ open node(head, ?next, ?value);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close nodes((*stack).head);
        //@ close stack(stack);
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req stack(stack) &*& p == neq_20;
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        filter_nodes(&raw mut (*stack).head, p);
        //@ close stack(stack);
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

unsafe fn neq_20(x: i32) -> bool
//@ req true;
//@ ens true;
{
    x != 20
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}