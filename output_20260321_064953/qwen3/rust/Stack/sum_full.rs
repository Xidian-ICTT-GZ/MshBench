//@ pred nodes(*mut Node node, list<i32> values) =
//@   match values {
//@     Nil => node == 0,
//@     Cons(v, vs) => node != 0 && *node |-> ?n &*& n.value == v &*& nodes(n.next, vs)
//@   };

//@ pred stack(*mut Stack s, list<i32> values) =
//@   s != 0 &*& *s |-> ?st &*& nodes(st.head, values);

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req nodes(node, ?vs);
//@ ens nodes(node, vs) &*& result == sum(vs);
{
    
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes(node, _);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close nodes(node, _);
    }
    //@ if (node == 0) { assert vs == Nil; } else { assert vs == Cons(?v, ?vs0); }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, Nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(0, Nil);
        //@ close stack(stack, Nil);
        
        stack
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, vs) &*& result == sum(vs);
    {
        
        let result = get_nodes_sum((*stack).head);
        
        result
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, Cons(value, vs));
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes(n, Cons(value, vs));
        //@ close stack(stack, Cons(value, vs));
        
        
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, Cons(?v, ?vs));
    //@ ens stack(stack, vs) &*& result == v;
    {
        
        let head = (*stack).head;
        //@ open stack(stack, _);
        //@ open nodes(head, _);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, vs);
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, _);
    //@ ens true;
    {
        //@ open stack(stack, _);
        //@ open nodes(?h, _);
        //@ while (h != 0) invariant nodes(h, ?vs) &*& vs != Nil;
        //@ {
        //@     open nodes(h, _);
        //@     let next = (*h).next;
        //@     dealloc(h as *mut u8, Layout::new::<Node>());
        //@     h = next;
        //@ }
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
        let sum = Stack::get_sum(s);
        
        let result1 = Stack::pop(s);
        
        let result2 = Stack::pop(s);
        
        Stack::dispose(s);
    }
}