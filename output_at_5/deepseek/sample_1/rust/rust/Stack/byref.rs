use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req node_predicate(*n);
//@ ens node_predicate(*n);
{
    if !(*n).is_null() {
        //@ open node_predicate(*n);
        let keep = p((**n).value);
        if keep {
            filter_nodes(&raw mut (**n).next, p);
        } else {
            let next_ = (**n).next;
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
        //@ close node_predicate(*n);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req node_predicate(n);
//@ ens true;
{
    if !n.is_null() {
        //@ open node_predicate(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack_predicate(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack_predicate(stack);
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack_predicate(stack);
    //@ ens stack_predicate(stack);
    {
        //@ open stack_predicate(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node_predicate(n);
        (*stack).head = n;
        //@ close stack_predicate(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack_predicate(stack);
    //@ ens stack_predicate(stack);
    {
        //@ open stack_predicate(stack);
        let head = (*stack).head;
        //@ open node_predicate(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack_predicate(stack);
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req stack_predicate(stack);
    //@ ens stack_predicate(stack);
    {
        //@ open stack_predicate(stack);
        filter_nodes(&raw mut (*stack).head, p);
        //@ close stack_predicate(stack);
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack_predicate(stack);
    //@ ens true;
    {
        //@ open stack_predicate(stack);
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

/*@
predicate node_predicate(Node *node) =
    node == 0 ? true : 
        struct_Node_padding(&(*node).next) &*&
        (*node).next |-> ?next &*&
        (*node).value |-> ?value &*&
        node_predicate(next);

predicate stack_predicate(Stack *stack) =
    struct_Stack_padding(&(*stack).head) &*&
    (*stack).head |-> ?head &*&
    node_predicate(head);
@*/