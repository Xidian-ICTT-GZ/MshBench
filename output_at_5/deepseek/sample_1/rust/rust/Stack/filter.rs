use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ predicate_ctor node_pred(n: *mut Node)() = 
//@     n != 0 ==> struct_Node_padding(n) &*& (*n).next |-> ?next &*& (*n).value |-> ?val &*& malloc_block_Node(n);

//@ predicate nodes(n: *mut Node) = 
//@     n == 0 ? true : node_pred(n)() &*& nodes((*n).next);

//@ predicate_ctor stack_pred(stack: *mut Stack)() = 
//@     stack != 0 ==> struct_Stack_padding(stack) &*& (*stack).head |-> ?head &*& malloc_block_Stack(stack) &*& nodes(head);

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
//@ req nodes(n);
//@ ens nodes(result);
{
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        //@ open nodes(n);
        //@ open node_pred(n)();
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);
            //@ close node_pred(n)();
            (*n).next = next;
            //@ close nodes(n);
            n
        } else {
            next = (*n).next;
            //@ close node_pred(n)();
            //@ close struct_Node_padding(n);
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            result
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req nodes(n);
//@ ens true;
{
    //@ open nodes(n);
    if !n.is_null() {
        //@ open node_pred(n)();
        dispose_nodes((*n).next);
        //@ close struct_Node_padding(n);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack_pred(result)();
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(0);
        //@ close stack_pred(stack)();
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack_pred(stack)() &*& malloc_block_Node(?n) &*& struct_Node_padding(n) &*& n != 0;
    //@ ens stack_pred(stack)();
    {
        //@ open stack_pred(stack)();
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node_pred(n)();
        //@ close nodes(n);
        (*stack).head = n;
        //@ close stack_pred(stack)();
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack_pred(stack)() &*& (*stack).head |-> ?head &*& head != 0 &*& node_pred(head)();
    //@ ens stack_pred(stack)() &*& result == old((*head).value);
    {
        //@ open stack_pred(stack)();
        let head = (*stack).head;
        //@ open node_pred(head)();
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close struct_Node_padding(head);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack_pred(stack)();
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req stack_pred(stack)();
    //@ ens stack_pred(stack)();
    {
        //@ open stack_pred(stack)();
        let head = filter_nodes((*stack).head, p);
        (*stack).head = head;
        //@ close stack_pred(stack)();
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack_pred(stack)();
    //@ ens true;
    {
        //@ open stack_pred(stack)();
        dispose_nodes((*stack).head);
        //@ close struct_Stack_padding(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool
//@ req true;
//@ ens true;
{
    x != 20
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let s = Stack::create();
        //@ close struct_Node_padding(?n1);
        Stack::push(s, 10);
        //@ close struct_Node_padding(?n2);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}