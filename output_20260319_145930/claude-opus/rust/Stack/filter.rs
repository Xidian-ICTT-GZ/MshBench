use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Nodes(n: *mut Node; count: i32) =
    if n == 0 {
        count == 0
    } else {
        alloc_block_Node(n) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?value &*&
        Nodes(next, ?rest) &*&
        count == rest + 1
    };

pred Stack(s: *mut Stack;) =
    alloc_block_Stack(s) &*&
    (*s).head |-> ?head &*&
    Nodes(head, _);

pred I32Pred(p: I32Predicate;) = true;
@*/

type I32Predicate = unsafe fn(i32) -> bool;

//@ req Nodes(n, _) &*& I32Pred(p);
//@ ens Nodes(result, _) &*& I32Pred(p);
unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
{
    //@ open Nodes(n, _);
    if n.is_null() {
        //@ close Nodes(std::ptr::null_mut(), 0);
        std::ptr::null_mut()
    } else {
        
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);
            
            
            (*n).next = next;
            //@ close Nodes(n, _);
            n
        } else {
            next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            result
        }
    }
}

//@ req Nodes(n, _);
//@ ens true;
unsafe fn dispose_nodes(n: *mut Node)
{
    //@ open Nodes(n, _);
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    //@ req true;
    //@ ens Stack(result);
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(std::ptr::null_mut(), 0);
        //@ close Stack(stack);
        stack
    }
    
    //@ req Stack(stack);
    //@ ens Stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open Stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n, _);
        //@ close Stack(stack);
    }

    //@ req Stack(stack) &*& (*stack).head |-> ?head &*& head != 0;
    //@ ens Stack(stack);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open Stack(stack);
        let head = (*stack).head;
        //@ open Nodes(head, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack);
        result
    }
    
    //@ req Stack(stack) &*& I32Pred(p);
    //@ ens Stack(stack) &*& I32Pred(p);
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    {
        //@ open Stack(stack);
        let head = filter_nodes((*stack).head, p);
        
        (*stack).head = head;
        //@ close Stack(stack);
    }
    
    //@ req Stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open Stack(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

//@ req true;
//@ ens true;
unsafe fn neq_20(x: i32) -> bool
{
    x != 20
}

//@ req true;
//@ ens true;
fn main()
{
    unsafe {
        //@ close I32Pred(neq_20);
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}